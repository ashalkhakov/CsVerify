using System.Collections.Generic;
using System.IO;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Text;

namespace CsVerify.Verifier
{
    /// <summary>
    /// The checked build (<c>csverify erase --checked</c>): erasure that keeps what of the specifications can run, as
    /// calls of the runtime's <c>CsVerify.Checked</c>, so a test (under Coyote, say) checks the program against them
    /// where they weren't proved, or holds them to what was:
    /// <list type="bullet">
    /// <item><c>Spec.Requires</c>, <c>Spec.Assert</c> and <c>Spec.Invariant</c> where they are; <c>Spec.Ensures</c> at
    /// each <c>return</c> and at the end of the body, with <c>Spec.Old</c> values taken where the postcondition is
    /// written (on entry);</item>
    /// <item>a lock's <c>[LockInvariant]</c>s when it is taken and when it is given back (a <c>lock</c> statement, in a
    /// <c>finally</c>; <c>Monitor.Enter</c>/<c>Exit</c>; <c>SemaphoreSlim.Wait</c>/<c>WaitAsync</c>/<c>Release</c>);</item>
    /// <item>each write and <c>Interlocked</c> change of an <c>[Atomic]</c> field with a step, as that step;</item>
    /// <item><c>[LockLevel]</c> at each <c>lock</c> statement: every lock the thread holds is lower;</item>
    /// <item><c>Monitor.Wait</c> and <c>SemaphoreSlim.Wait</c>/<c>WaitAsync</c> report the wait (Checked.Waiting, Woken).</item>
    /// </list>
    /// A condition stays out when it can't run (it uses ghost state: Seq, ObjSet, [GhostFunction]s, Spec.Result...),
    /// or when other threads may change what it reads while it is evaluated, so that the run-time value wouldn't be
    /// the one the proof speaks of: an [Atomic] or volatile field, or a [GuardedBy] field outside a lock on its lock.
    /// </summary>
    public static partial class Erasure
    {
        private sealed partial class FileEraser
        {
            private const string Checked = "global::CsVerify.Checked.";
            private readonly HashSet<StatementSyntax> _handled = new HashSet<StatementSyntax>();
            private int _olds;

            private void CheckedNode(SyntaxNode node)
            {
                switch (node)
                {
                    case BaseMethodDeclarationSyntax m when m.Body != null && _model.GetDeclaredSymbol(m) is IMethodSymbol ms && !IsErasedMethod(ms):
                        Postconditions(m.Body, ms);
                        break;
                    case LocalFunctionStatementSyntax lf when lf.Body != null && _model.GetDeclaredSymbol(lf) is IMethodSymbol ls:
                        Postconditions(lf.Body, ls);
                        break;
                    case AccessorDeclarationSyntax a when a.Body != null && _model.GetDeclaredSymbol(a) is IMethodSymbol accessor:
                        Postconditions(a.Body, accessor);
                        break;
                    case ExpressionStatementSyntax es:
                        CheckedStatement(es);
                        break;
                    case LockStatementSyntax lk:
                        LockStatement(lk);
                        break;
                    case InvocationExpressionSyntax inv:
                        CheckedCall(inv);
                        break;
                }
            }

            // ------------------------------------------------------------------ contracts

            private void CheckedStatement(ExpressionStatementSyntax es)
            {
                if (_handled.Contains(es)) return;
                if (es.Expression is InvocationExpressionSyntax inv && _model.GetSymbolInfo(inv).Symbol is IMethodSymbol m && SpecSymbols.IsSpecClass(m.ContainingType))
                {
                    var kind = m.Name;
                    if ((kind == "Requires" || kind == "Assert" || kind == "Invariant") && inv.ArgumentList.Arguments.Count == 1)
                    {
                        var cond = inv.ArgumentList.Arguments[0].Expression;
                        if (!CanRun(cond, es, olds: false)) return;
                        _handled.Add(es);
                        Replace(es.Span, KeepLines(es, $"{Checked}{kind}({Render(cond, null)}, {Message(cond)});"));
                    }
                    return;
                }
                if (es.Expression is AssignmentExpressionSyntax asg && asg.IsKind(SyntaxKind.SimpleAssignmentExpression) &&
                    _model.GetSymbolInfo(asg.Left).Symbol is IFieldSymbol f && StepRef(f, es) is string step && !InConstructorOf(es, f))
                {
                    // field = value: a step from what it overwrites (the write stays the program's own, a field write)
                    int n = _olds++;
                    Replace(TextSpan.FromBounds(asg.Left.SpanStart, asg.Right.SpanStart), $"{{ var __cv_value{n} = ");
                    Insert(asg.Right.Span.End, $"; var __cv_was{n} = {asg.Left}; {asg.Left} = __cv_value{n}; {Checked}Step({step}(__cv_was{n}, __cv_value{n}), {Message(asg)}); }}");
                    Replace(es.SemicolonToken.Span, "");
                }
                if (Lock(Called(es.Expression, out bool awaited), awaited) is (var invariant, bool taking))
                {
                    // Monitor.Enter(x), x.Wait(), await x.WaitAsync(): the invariant holds after; Monitor.Exit(x), x.Release(): before
                    Insert(es.SpanStart, "{ " + (taking ? "" : invariant + " "), Depth(es));
                    Insert(es.Span.End, (taking ? " " + invariant : "") + " }", -Depth(es));
                }
            }

            /// <summary>
            /// Spec.Ensures in a body: checked at each return of it (not of its lambdas and local functions), and at its
            /// end if that is reached; Spec.Old(e) taken where the postcondition is written.
            /// </summary>
            private void Postconditions(BlockSyntax body, IMethodSymbol method)
            {
                if (method.IsAsync && method.ReturnsVoid) return;
                var ensures = body.Statements.OfType<ExpressionStatementSyntax>()
                    .Select(es => (es, inv: es.Expression as InvocationExpressionSyntax))
                    .Where(x => x.inv != null && _model.GetSymbolInfo(x.inv).Symbol is IMethodSymbol m && SpecSymbols.IsSpecClass(m.ContainingType) && m.Name == "Ensures")
                    .ToList();
                if (ensures.Count == 0) return;
                var own = body.DescendantNodes(n => !(n is AnonymousFunctionExpressionSyntax || n is LocalFunctionStatementSyntax)).ToList();
                if (own.OfType<YieldStatementSyntax>().Any()) return;
                var returns = own.OfType<ReturnStatementSyntax>().ToList();
                // the value returned: of the method, or of its task
                ITypeSymbol result = method.ReturnsVoid ? null : method.ReturnType;
                if (method.IsAsync && result is INamedTypeSymbol task)
                    result = task.TypeArguments.Length == 1 ? task.TypeArguments[0] : null;
                bool inStruct = method.ContainingType?.IsValueType == true && !method.IsStatic;

                var checks = new List<(string open, string close, string statement)>();
                foreach (var (es, inv) in ensures)
                {
                    _handled.Add(es);
                    var m = (IMethodSymbol)_model.GetSymbolInfo(inv).Symbol;
                    var arg = inv.ArgumentList.Arguments.Count == 1 ? inv.ArgumentList.Arguments[0].Expression : null;
                    var olds = new Dictionary<TextSpan, string>();
                    var declarations = "";
                    bool runs = arg != null && returns.All(r => CanRun(arg, r, olds: true)) && (returns.Count > 0 || CanRun(arg, null, olds: true));
                    if (runs)
                        foreach (var old in arg.DescendantNodes().OfType<InvocationExpressionSyntax>().Where(IsOld))
                        {
                            var name = "__cv_old" + _olds++;
                            olds[old.Span] = name;
                            declarations += $"var {name} = {Render(old.ArgumentList.Arguments[0].Expression, null)}; ";
                        }
                    Replace(es.Span, KeepLines(es, declarations));
                    if (!runs) continue;
                    if (m.IsGenericMethod && arg is LambdaExpressionSyntax lambda && result != null && !inStruct)
                    {
                        var r = m.TypeArguments[0].ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat);
                        checks.Add(($"{Checked}Ensures<{r}>(", $", {Render(lambda, olds)}, {Message(arg)})", null));
                    }
                    else if (!m.IsGenericMethod && result == null)
                        checks.Add((null, null, $"{Checked}Ensures({Render(arg, olds)}, {Message(arg)});"));
                    else if (!m.IsGenericMethod && !inStruct)
                    {
                        var r = result.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat);
                        checks.Add(($"{Checked}Ensures<{r}>(", $", _ => {Render(arg, olds)}, {Message(arg)})", null));
                    }
                }
                var values = checks.Where(c => c.open != null).ToList();
                var statements = string.Concat(checks.Where(c => c.statement != null).Select(c => c.statement + " "));
                foreach (var ret in returns)
                {
                    if (ret.Expression != null && values.Count > 0)
                    {
                        Insert(ret.Expression.SpanStart, string.Concat(values.Select(v => v.open)));
                        Insert(ret.Expression.Span.End, string.Concat(Enumerable.Reverse(values).Select(v => v.close)));
                    }
                    else if (ret.Expression == null && statements.Length > 0)
                    {
                        Insert(ret.SpanStart, "{ " + statements, Depth(ret));
                        Insert(ret.Span.End, " }", -Depth(ret));
                    }
                }
                if (statements.Length > 0 && EndReached(body))
                    Insert(body.CloseBraceToken.SpanStart, statements, int.MinValue);
            }

            private bool EndReached(BlockSyntax body) =>
                body.Statements.Count == 0 || _model.AnalyzeControlFlow(body.Statements.First(), body.Statements.Last()) is ControlFlowAnalysis cf && cf.Succeeded && cf.EndPointIsReachable;

            private bool IsOld(InvocationExpressionSyntax inv) =>
                _model.GetSymbolInfo(inv).Symbol is IMethodSymbol m && SpecSymbols.IsSpecClass(m.ContainingType) && m.Name == "Old" && inv.ArgumentList.Arguments.Count == 1;

            /// <summary>
            /// Can the condition run at <paramref name="site"/> (null: on entry), giving the value the proof speaks of?
            /// Not with ghost state, nor with what other threads may change meanwhile.
            /// </summary>
            private bool CanRun(ExpressionSyntax cond, SyntaxNode site, bool olds)
            {
                foreach (var n in cond.DescendantNodesAndSelf())
                {
                    // (inside Spec.Old(...), what is read is read on entry)
                    bool inOld = olds && n.Ancestors().TakeWhile(a => a != cond).OfType<InvocationExpressionSyntax>().Any(IsOld);
                    var at = inOld ? null : site;
                    var symbol = _model.GetSymbolInfo(n).Symbol;
                    if (symbol is ITypeSymbol || symbol is INamespaceSymbol) continue; // (a name, as Spec in Spec.Old)
                    if (n is ExpressionSyntax e && _model.GetTypeInfo(e).Type is ITypeSymbol t && (IsProofType(t) || InCsVerify(t))) return false;
                    switch (symbol)
                    {
                        case IMethodSymbol m:
                            if (SpecSymbols.IsSpecClass(m.ContainingType))
                            {
                                if (m.Name == "Forall" && m.Parameters.Length == 3) break;
                                if (m.Name == "Old" && olds) break;
                                return false;
                            }
                            if (IsErasedMethod(m) || InCsVerify(m.ContainingType)) return false;
                            break;
                        case IFieldSymbol f:
                            if (Atomics.IsAtomic(f) || f.IsVolatile) return false;
                            if (GuardOf(f) is string guard && !(at != null && HeldAt(at, f.ContainingType, guard))) return false;
                            break;
                        case IPropertySymbol p when InCsVerify(p.ContainingType):
                            return false;
                        case IParameterSymbol p when p.RefKind != RefKind.None:
                            return false;
                        // (Spec.Old of a lambda's variable, as in Spec.Forall(0, n, i => a[i] == Spec.Old(a[i])), isn't one value on entry)
                        case ISymbol v when inOld && (v is IParameterSymbol || v is ILocalSymbol) && v.DeclaringSyntaxReferences.Any(r => cond.Span.Contains(r.Span)):
                            return false;
                    }
                }
                return true;
            }

            private static bool InCsVerify(ITypeSymbol t) =>
                t != null && t.ContainingNamespace?.ToDisplayString() == "CsVerify" && t.Name != "Ptr";

            private static string GuardOf(IFieldSymbol f) =>
                f.GetAttributes().FirstOrDefault(a => a.AttributeClass?.Name == "GuardedByAttribute")?.ConstructorArguments.FirstOrDefault().Value as string;

            /// <summary>Is <paramref name="at"/> inside a lock statement on the lock field <paramref name="guard"/>?</summary>
            private bool HeldAt(SyntaxNode at, INamedTypeSymbol type, string guard) =>
                at.AncestorsAndSelf().OfType<LockStatementSyntax>().Any(l =>
                    _model.GetSymbolInfo(l.Expression).Symbol is IFieldSymbol lf && lf.Name == guard && SymbolEqualityComparer.Default.Equals(lf.ContainingType, type));

            // ------------------------------------------------------------------ locks

            /// <summary>A lock statement: its invariants checked on entering and on leaving (in a finally), its level on taking it.</summary>
            private void LockStatement(LockStatementSyntax lk)
            {
                var (field, receiver, index) = LockField(lk.Expression);
                if (field == null) return;
                var invariant = Invariants(field, receiver, lk);
                var level = LevelOf(field);
                string taking = "", took = "", released = "";
                if (level is (int n, var orderedBy))
                {
                    bool ordered = orderedBy != null || index != null;
                    var order = index != null ? $"(long)({index})" : orderedBy != null ? $"(long){Prefix(receiver)}{orderedBy}" : "0L";
                    var name = SymbolDisplay.FormatLiteral(lk.Expression.ToString(), true);
                    taking = $"{Checked}Taking({n}, {order}, {(ordered ? "true" : "false")}, {name}); ";
                    took = $"{Checked}Took({n}, {order}, {name}); ";
                    released = $" {Checked}Released({n}, {order});";
                }
                if (invariant == null && taking.Length == 0) return;
                int depth = Depth(lk);
                if (taking.Length > 0)
                {
                    Insert(lk.SpanStart, "{ " + taking, depth);
                    Insert(lk.Span.End, " }", -depth);
                }
                // (inside the block around the statement, which ends where the body does)
                Insert(lk.Statement.SpanStart, "{ " + took + (invariant != null ? invariant + " " : "") + "try { ", depth + 1);
                Insert(lk.Statement.Span.End, " } finally {" + (invariant != null ? " " + invariant : "") + released + " } }", -(depth + 1));
            }

            /// <summary>
            /// Monitor.Enter/Exit(x), x.Wait()/WaitAsync()/Release() of a SemaphoreSlim, on a lock field with invariants:
            /// the check, and whether the call takes the lock (the check goes after) or gives it back (before).
            /// </summary>
            /// <summary>The call a statement makes: <c>f(...)</c>, or <c>await f(...)</c> (through ConfigureAwait).</summary>
            private static InvocationExpressionSyntax Called(ExpressionSyntax e, out bool awaited)
            {
                awaited = false;
                if (e is AwaitExpressionSyntax aw)
                {
                    awaited = true;
                    e = aw.Expression;
                    if (e is InvocationExpressionSyntax ca && ca.Expression is MemberAccessExpressionSyntax cm && cm.Name.Identifier.Text == "ConfigureAwait") e = cm.Expression;
                }
                return e as InvocationExpressionSyntax;
            }

            private (string invariant, bool taking)? Lock(InvocationExpressionSyntax inv, bool awaited)
            {
                if (inv == null || !(_model.GetSymbolInfo(inv).Symbol is IMethodSymbol m) || !m.ReturnsVoid && m.ReturnType.Name != "Task") return null;
                var type = m.ContainingType?.ToDisplayString();
                ExpressionSyntax target;
                bool taking;
                if (type == "System.Threading.Monitor" && (m.Name == "Enter" || m.Name == "Exit") && m.Parameters.Length == 1)
                {
                    target = inv.ArgumentList.Arguments[0].Expression;
                    taking = m.Name == "Enter";
                }
                else if (type == "System.Threading.SemaphoreSlim" && inv.Expression is MemberAccessExpressionSyntax ma &&
                         (m.Name == "Wait" || m.Name == "WaitAsync" || m.Name == "Release" && m.Parameters.Length == 0) &&
                         m.Parameters.All(p => p.Type.Name == "CancellationToken") && (m.Name != "WaitAsync" || awaited))
                {
                    target = ma.Expression;
                    taking = m.Name != "Release";
                }
                else return null;
                var (field, receiver, _) = LockField(target);
                if (field == null) return null;
                return Invariants(field, receiver, inv) is string invariant ? (invariant, taking) : ((string, bool)?)null;
            }

            /// <summary>The lock field an expression reads (x, this.x, o.x, Type.x, or an element of x[i]), and the rest.</summary>
            private (IFieldSymbol field, ExpressionSyntax receiver, string index) LockField(ExpressionSyntax e)
            {
                string index = null;
                if (e is ElementAccessExpressionSyntax ea && ea.ArgumentList.Arguments.Count == 1)
                {
                    index = ea.ArgumentList.Arguments[0].ToString();
                    e = ea.Expression;
                }
                if (!(_model.GetSymbolInfo(e).Symbol is IFieldSymbol f)) return (null, null, null);
                var receiver = e is MemberAccessExpressionSyntax ma && !(ma.Expression is ThisExpressionSyntax) && !f.IsStatic ? ma.Expression : null;
                return (f, receiver, index);
            }

            private static string Prefix(ExpressionSyntax receiver) => receiver == null ? "" : $"({receiver}).";

            /// <summary>The check of the [LockInvariant]s of the lock field (those that can run), on the object locked.</summary>
            private string Invariants(IFieldSymbol field, ExpressionSyntax receiver, SyntaxNode at)
            {
                var calls = field.ContainingType.GetMembers().OfType<IMethodSymbol>()
                    .Where(m => m.Parameters.Length == 0 && m.ReturnType.SpecialType == SpecialType.System_Boolean && !IsErasedMethod(m) &&
                                m.GetAttributes().Any(a => a.AttributeClass?.Name == "LockInvariantAttribute" && a.ConstructorArguments.FirstOrDefault().Value as string == field.Name) &&
                                _model.IsAccessible(at.SpanStart, m) && (m.IsStatic == field.IsStatic))
                    .Select(m => (m.IsStatic ? m.ContainingType.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat) + "." : Prefix(receiver)) + m.Name + "()")
                    .ToList();
                if (calls.Count == 0) return null;
                var what = SymbolDisplay.FormatLiteral($"{string.Join(" && ", calls)} ({field.Name}) {Where(at)}", true);
                return $"{Checked}LockInvariant({string.Join(" && ", calls)}, {what});";
            }

            private static (int level, string orderedBy)? LevelOf(IFieldSymbol f)
            {
                var a = f.GetAttributes().FirstOrDefault(x => x.AttributeClass?.Name == "LockLevelAttribute");
                if (a == null || !(a.ConstructorArguments.FirstOrDefault().Value is int level)) return null;
                return (level, a.NamedArguments.FirstOrDefault(kv => kv.Key == "OrderedBy").Value.Value as string);
            }

            // ------------------------------------------------------------------ calls: Interlocked steps, waits

            private void CheckedCall(InvocationExpressionSyntax inv)
            {
                if (!(_model.GetSymbolInfo(inv).Symbol is IMethodSymbol m)) return;
                var type = m.ContainingType?.ToDisplayString();
                var args = inv.ArgumentList.Arguments;
                if (type == "System.Threading.Interlocked" && args.Count >= 1 && args[0].RefKindKeyword.IsKind(SyntaxKind.RefKeyword) &&
                    (m.Name == "CompareExchange" && args.Count == 3 || m.Name == "Exchange" && args.Count == 2 || m.Name == "Add" && args.Count == 2 ||
                     (m.Name == "Increment" || m.Name == "Decrement") && args.Count == 1) &&
                    _model.GetSymbolInfo(args[0].Expression).Symbol is IFieldSymbol f && StepRef(f, inv) is string step &&
                    (f.Type.SpecialType == SpecialType.System_Int32 || f.Type.SpecialType == SpecialType.System_Int64 || f.Type.IsReferenceType && m.Name != "Add" && m.Name != "Increment" && m.Name != "Decrement"))
                {
                    Replace(inv.Expression.Span, Checked + m.Name);
                    Insert(inv.ArgumentList.CloseParenToken.SpanStart, $", {step}, {Message(inv)}");
                    return;
                }
                if (type == "System.Threading.Monitor" && m.Name == "Wait" && (args.Count == 1 || args.Count == 2 && m.Parameters[1].Type.SpecialType == SpecialType.System_Int32))
                {
                    Replace(inv.Expression.Span, Checked + "MonitorWait");
                    return;
                }
                if (type == "System.Threading.SemaphoreSlim" && (m.Name == "Wait" && m.ReturnsVoid || m.Name == "WaitAsync" && m.ReturnType.Name == "Task" && !m.ReturnType.IsGenericType()) &&
                    m.Parameters.All(p => p.Type.Name == "CancellationToken") && inv.Expression is MemberAccessExpressionSyntax ma)
                {
                    var call = m.Name == "Wait" ? "SemaphoreWait" : "SemaphoreWaitAsync";
                    Replace(TextSpan.FromBounds(inv.SpanStart, inv.ArgumentList.OpenParenToken.Span.End), $"{Checked}{call}({ma.Expression}{(args.Count > 0 ? ", " : "")}");
                }
            }

            /// <summary>The step of an [Atomic] field, as a method group that can be named here; null if it has none.</summary>
            private string StepRef(IFieldSymbol f, SyntaxNode at)
            {
                if (!Atomics.IsAtomic(f) || !(Atomics.StepOf(f) is IMethodSymbol step) || !step.IsStatic || !_model.IsAccessible(at.SpanStart, step)) return null;
                return step.ContainingType.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat) + "." + step.Name;
            }

            /// <summary>In a constructor of the field's type: the object isn't shared yet, and its first values are no steps.</summary>
            private bool InConstructorOf(SyntaxNode at, IFieldSymbol f) =>
                at.Ancestors().OfType<ConstructorDeclarationSyntax>().FirstOrDefault() is ConstructorDeclarationSyntax c &&
                _model.GetDeclaredSymbol(c) is IMethodSymbol cm && SymbolEqualityComparer.Default.Equals(cm.ContainingType, f.ContainingType);

            // ------------------------------------------------------------------ text

            /// <summary>The expression's text, with the given spans in it replaced (Spec.Old values by their locals) and Spec.Forall run.</summary>
            private string Render(SyntaxNode e, Dictionary<TextSpan, string> subs)
            {
                var all = new Dictionary<TextSpan, string>(subs ?? new Dictionary<TextSpan, string>());
                foreach (var inv in e.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>())
                    if (_model.GetSymbolInfo(inv).Symbol is IMethodSymbol m && SpecSymbols.IsSpecClass(m.ContainingType) && m.Name == "Forall")
                        all[inv.Expression.Span] = Checked + "Forall";
                var text = _text.ToString(e.Span);
                foreach (var kv in all.Where(kv => e.Span.Contains(kv.Key)).OrderByDescending(kv => kv.Key.Start))
                {
                    int at = kv.Key.Start - e.SpanStart;
                    if (all.Keys.Any(k => k != kv.Key && k.Contains(kv.Key))) continue; // inside another replaced span
                    text = text.Substring(0, at) + kv.Value + text.Substring(at + kv.Key.Length);
                }
                return "(" + System.Text.RegularExpressions.Regex.Replace(text, @"\s*\r?\n\s*", " ") + ")";
            }

            private string Message(SyntaxNode e) =>
                SymbolDisplay.FormatLiteral(System.Text.RegularExpressions.Regex.Replace(e.ToString(), @"\s+", " ") + " " + Where(e), true);

            private string Where(SyntaxNode e) =>
                $"({Path.GetFileName(_tree.FilePath)}:{e.GetLocation().GetLineSpan().StartLinePosition.Line + 1})";

            /// <summary>The replacement of a statement, with as many line breaks as it had, so the lines after it keep their numbers.</summary>
            private string KeepLines(SyntaxNode original, string replacement)
            {
                int had = _text.ToString(original.Span).Count(c => c == '\n');
                return replacement.Replace("\r", "").Replace("\n", " ") + new string('\n', had);
            }

            /// <summary>
            /// The order of what is inserted around a node: opening text goes in by increasing depth, closing text by
            /// decreasing, so what wraps an inner node is inside what wraps an outer one (two steps a level, for two
            /// wrappings of one node).
            /// </summary>
            private static int Depth(SyntaxNode n) => 2 * n.Ancestors().Count();
        }
    }

    internal static class TypeSymbolExtensions
    {
        public static bool IsGenericType(this ITypeSymbol t) => t is INamedTypeSymbol n && n.IsGenericType;
    }
}
