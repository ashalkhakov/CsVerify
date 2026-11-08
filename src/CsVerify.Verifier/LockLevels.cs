using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace CsVerify.Verifier
{
    /// <summary>
    /// The order locks are taken in (Chalice's and Viper's lock levels, Clang's ACQUIRED_AFTER): a lock field's
    /// <c>[LockLevel]</c>, and what locks code may take, by itself or through what it calls or waits for. A thread that
    /// takes locks only in increasing order of level can't be part of a cycle of threads waiting on each other, so a lock
    /// taken, a call made, or a task waited for while a lock is held must take only higher locks (CSV1025; see
    /// MethodVerifier.LockLevels).
    /// </summary>
    internal sealed class LockLevels
    {
        private readonly Compilation _compilation;
        private readonly LockGuards _locks;
        private readonly IReadOnlyList<INamedTypeSymbol> _types;
        private readonly Dictionary<IMethodSymbol, Summary> _memo = new Dictionary<IMethodSymbol, Summary>(SymbolEqualityComparer.Default);

        public LockLevels(Compilation compilation, LockGuards locks, IReadOnlyList<INamedTypeSymbol> types)
        {
            _compilation = compilation;
            _locks = locks;
            _types = types;
        }

        /// <summary>A lock code takes: its field (or the array whose element it is), whether it's of the object the code is on, and the method that takes it.</summary>
        public sealed class Take
        {
            public ISymbol Lock;
            public bool Element, OnThis, Semaphore;
            public IMethodSymbol In;
        }

        /// <summary>What code may take: these locks, and, if <see cref="Unknown"/> says what, any lock at all.</summary>
        public sealed class Summary
        {
            public readonly List<Take> Taken = new List<Take>();
            public string Unknown;
            public bool IsEmpty => Taken.Count == 0 && Unknown == null;

            public void Add(Take t)
            {
                if (!Taken.Any(x => SymbolEqualityComparer.Default.Equals(x.Lock, t.Lock) && x.Element == t.Element && x.OnThis == t.OnThis)) Taken.Add(t);
            }
        }

        /// <summary>A lock taken at a point of the code: what it is a lock of, and on what, as written ("this", "static", or the expression).</summary>
        public sealed class Acquired
        {
            public ISymbol Lock;
            public bool Element, Semaphore;
            public string Receiver;
            public SyntaxNode At, Expression;
        }

        public static int? Level(ISymbol lockSymbol) =>
            lockSymbol is IFieldSymbol f && f.GetAttributes().FirstOrDefault(a => a.AttributeClass?.Name == "LockLevelAttribute") is AttributeData a &&
            a.ConstructorArguments.FirstOrDefault().Value is int n ? n : (int?)null;

        /// <summary>The int field two locks of this field on different objects are ordered by, or null.</summary>
        public static IFieldSymbol OrderedBy(ISymbol lockSymbol)
        {
            if (!(lockSymbol is IFieldSymbol f) || !(f.GetAttributes().FirstOrDefault(a => a.AttributeClass?.Name == "LockLevelAttribute") is AttributeData a)) return null;
            var named = a.NamedArguments.FirstOrDefault(x => x.Key == "OrderedBy").Value.Value as string;
            return named == null || !(f.Type is INamedTypeSymbol) ? null : f.ContainingType.GetMembers(named).OfType<IFieldSymbol>().FirstOrDefault(k => k.Type.SpecialType == SpecialType.System_Int32);
        }

        /// <summary>Is it said to take no locks: the method, its property, its type, or what it overrides or implements?</summary>
        public bool TakesNoLocks(IMethodSymbol m)
        {
            var seen = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
            bool Said(IMethodSymbol x)
            {
                x = x.OriginalDefinition;
                if (!seen.Add(x)) return false;
                if (SpecSymbols.HasAttribute(x, "TakesNoLocksAttribute") || x.AssociatedSymbol != null && SpecSymbols.HasAttribute(x.AssociatedSymbol, "TakesNoLocksAttribute") ||
                    x.ContainingType != null && SpecSymbols.HasAttribute(x.ContainingType, "TakesNoLocksAttribute"))
                    return true;
                if (x.OverriddenMethod != null && Said(x.OverriddenMethod)) return true;
                if (x.IsStatic || x.ContainingType == null) return false;
                foreach (var iface in x.ContainingType.AllInterfaces)
                    foreach (var im in iface.GetMembers().OfType<IMethodSymbol>())
                        if (SymbolEqualityComparer.Default.Equals(x.ContainingType.FindImplementationForInterfaceMember(im)?.OriginalDefinition, x) && Said(im)) return true;
                return false;
            }
            return Said(m);
        }

        public static bool TakesNoLocks(ITypeSymbol delegateType) => delegateType != null && SpecSymbols.HasAttribute(delegateType.OriginalDefinition, "TakesNoLocksAttribute");

        // ---- where locks are taken, and held ----

        /// <summary>What a lock statement's expression locks: a field, an array's element, or something else (then the symbol may be a local, a parameter, or null).</summary>
        public static (ISymbol sym, bool element, string receiver) LockTarget(ExpressionSyntax e, SemanticModel model)
        {
            if (e is ElementAccessExpressionSyntax ea) return (model.GetSymbolInfo(ea.Expression).Symbol, true, ea.Expression.ToString());
            var s = model.GetSymbolInfo(e).Symbol;
            if (s is IFieldSymbol f)
                return (f, false, f.IsStatic ? "static" : e is MemberAccessExpressionSyntax ma && !(ma.Expression is ThisExpressionSyntax) ? ma.Expression.ToString() : "this");
            return (s, false, e.ToString());
        }

        /// <summary>The lock this node takes, if it is a lock statement, the statement that takes a semaphore before its try, or a using that holds one.</summary>
        public Acquired AcquiredAt(SyntaxNode n, SemanticModel model)
        {
            switch (n)
            {
                case LockStatementSyntax l:
                    var (sym, element, receiver) = LockTarget(l.Expression, model);
                    return new Acquired { Lock = sym, Element = element, Receiver = receiver, At = l, Expression = l.Expression };
                case StatementSyntax st when LockGuards.TryAfter(st) is TryStatementSyntax t && _locks.GateOfTry(t, model) is IFieldSymbol gate && _locks.IsMutexGate(gate):
                    return new Acquired { Lock = gate, Semaphore = true, Receiver = gate.IsStatic ? "static" : _locks.TryOwner(t, gate, model), At = st, Expression = st };
                case UsingStatementSyntax u when _locks.GateOfUsing(u, model) is IFieldSymbol g:
                    return new Acquired { Lock = g, Semaphore = true, Receiver = g.IsStatic ? "static" : _locks.UsingOwner(u.Expression ?? u.Declaration.Variables[0].Initializer.Value, model), At = u, Expression = u };
                case LocalDeclarationStatementSyntax d when _locks.GateOfUsing(d, model) is IFieldSymbol g2:
                    return new Acquired { Lock = g2, Semaphore = true, Receiver = g2.IsStatic ? "static" : _locks.UsingOwner(d.Declaration.Variables[0].Initializer.Value, model), At = d, Expression = d };
            }
            return null;
        }

        /// <summary>The locks held at a node, by the code around it in its function (not outside a lambda or local function, which run who knows when), innermost first.</summary>
        public IEnumerable<Acquired> HeldAt(SyntaxNode n, SyntaxNode root, SemanticModel model)
        {
            for (var p = n.Parent; p != null; p = p.Parent)
            {
                switch (p)
                {
                    case LockStatementSyntax l when l.Statement.Span.Contains(n.Span):
                        yield return AcquiredAt(l, model);
                        break;
                    case TryStatementSyntax t when _locks.GateOfTry(t, model) is IFieldSymbol gate && _locks.IsMutexGate(gate) && _locks.HeldParts(t, model).Any(h => h.Span.Contains(n.Span)):
                        if (AcquiredAt(((BlockSyntax)t.Parent).Statements[((BlockSyntax)t.Parent).Statements.IndexOf(t) - 1], model) is Acquired a) yield return a;
                        break;
                    case UsingStatementSyntax u when u.Statement.Span.Contains(n.Span) && AcquiredAt(u, model) is Acquired au:
                        yield return au;
                        break;
                    case BlockSyntax b:
                        foreach (var (_, at) in _locks.UsingsBefore(n, b, model).Reverse())
                            if (AcquiredAt(at, model) is Acquired ad) yield return ad;
                        break;
                    case AnonymousFunctionExpressionSyntax _:
                    case LocalFunctionStatementSyntax _:
                        yield break;
                }
                if (p == root) yield break;
            }
        }

        // ---- what code may take ----

        /// <summary>The locks a method may take, by itself and through what it calls and waits for.</summary>
        public Summary Of(IMethodSymbol m)
        {
            m = m.OriginalDefinition;
            if (_memo.TryGetValue(m, out var known)) return known;
            var s = new Summary();
            var work = new Walk(this, s);
            work.Push(m, true);
            work.Run();
            return _memo[m] = s;
        }

        /// <summary>What a method's own body may take, even if it says it takes none (to check that it doesn't).</summary>
        public Summary OfBody(IMethodSymbol m)
        {
            var s = new Summary();
            var work = new Walk(this, s);
            work.Push(m, true, trustSaid: false);
            work.Run();
            return s;
        }

        /// <summary>The locks a lambda (or other code) may take when it runs.</summary>
        public Summary OfRegion(SyntaxNode region, SemanticModel model, IMethodSymbol inMethod)
        {
            var s = new Summary();
            var work = new Walk(this, s);
            work.Scan(region, model, true, inMethod);
            work.Run();
            return s;
        }

        /// <summary>What one node of code does by calling: the methods, accessors and lambdas it runs, and what they may take.</summary>
        public Summary OfCall(SyntaxNode node, SemanticModel model, IMethodSymbol inMethod)
        {
            var s = new Summary();
            var work = new Walk(this, s);
            work.Call(node, model, true, inMethod, true);
            work.Run();
            return s;
        }

        /// <summary>The methods, overrides and implementations a call of this one may run, in the program's source.</summary>
        private IEnumerable<IMethodSymbol> Bodies(IMethodSymbol m)
        {
            m = m.OriginalDefinition;
            if (m.DeclaringSyntaxReferences.Length > 0 && !m.IsAbstract) yield return m;
            if (!Engine.IsOverridable(m)) yield break;
            foreach (var t in _types)
            {
                if (m.ContainingType.TypeKind == TypeKind.Interface)
                {
                    if (t.AllInterfaces.Any(i => SymbolEqualityComparer.Default.Equals(i.OriginalDefinition, m.ContainingType)) &&
                        t.FindImplementationForInterfaceMember(m) is IMethodSymbol impl && impl.DeclaringSyntaxReferences.Length > 0 && !impl.IsAbstract)
                        yield return impl.OriginalDefinition;
                    continue;
                }
                foreach (var o in t.GetMembers(m.Name).OfType<IMethodSymbol>())
                    for (var b = o.OverriddenMethod; b != null; b = b.OverriddenMethod)
                        if (SymbolEqualityComparer.Default.Equals(b.OriginalDefinition, m))
                        {
                            if (o.DeclaringSyntaxReferences.Length > 0 && !o.IsAbstract) yield return o.OriginalDefinition;
                            break;
                        }
            }
        }

        private static readonly HashSet<string> Starters = new HashSet<string> { "Run", "StartNew", "ContinueWith", "QueueUserWorkItem", "UnsafeQueueUserWorkItem" };

        /// <summary>A lambda given to a library call that runs it before returning (not one that starts it as a task or thread).</summary>
        private static bool RunsAtOnce(SyntaxNode lambda, SemanticModel model)
        {
            if (!(lambda.Parent is ArgumentSyntax arg) || !(arg.Parent?.Parent is InvocationExpressionSyntax inv)) return false;
            return model.GetSymbolInfo(inv).Symbol is IMethodSymbol m && !Starters.Contains(m.Name);
        }

        private static ExpressionSyntax Stripped(ExpressionSyntax e)
        {
            if (e is InvocationExpressionSyntax ca && ca.Expression is MemberAccessExpressionSyntax cm && cm.Name.Identifier.Text == "ConfigureAwait") e = cm.Expression;
            while (e is ParenthesizedExpressionSyntax p) e = p.Expression;
            return e;
        }

        private static bool IsWaitable(ITypeSymbol t)
        {
            var name = t?.OriginalDefinition.ToDisplayString() ?? "";
            return name.StartsWith("System.Threading.Tasks.Task") || name.StartsWith("System.Threading.Tasks.ValueTask") || name == "System.Threading.Thread";
        }

        /// <summary>
        /// The tasks or threads a node waits for: by <c>await</c>, <c>Wait()</c>, <c>Result</c>, <c>GetResult()</c>,
        /// <c>Join()</c>, or <c>Task.WhenAll</c> and its kind. Not one made right there by a call, whose call is looked at as such.
        /// </summary>
        public static IEnumerable<ExpressionSyntax> WaitedFor(SyntaxNode n, SemanticModel model)
        {
            ExpressionSyntax one = null;
            switch (n)
            {
                case AwaitExpressionSyntax aw: one = Stripped(aw.Expression); break;
                case MemberAccessExpressionSyntax ma when ma.Name.Identifier.Text == "Result" && IsWaitable(model.GetTypeInfo(ma.Expression).Type): one = ma.Expression; break;
                case InvocationExpressionSyntax inv when inv.Expression is MemberAccessExpressionSyntax im:
                    var name = im.Name.Identifier.Text;
                    if ((name == "Wait" || name == "Join") && IsWaitable(model.GetTypeInfo(im.Expression).Type)) one = im.Expression;
                    else if (name == "GetResult" && im.Expression is InvocationExpressionSyntax ga && ga.Expression is MemberAccessExpressionSyntax gm && gm.Name.Identifier.Text == "GetAwaiter") one = gm.Expression;
                    else if ((name == "WhenAll" || name == "WhenAny" || name == "WaitAll" || name == "WaitAny") && model.GetSymbolInfo(inv).Symbol is IMethodSymbol wm && wm.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task")
                    {
                        foreach (var a in inv.ArgumentList.Arguments)
                            if (!(Stripped(a.Expression) is InvocationExpressionSyntax || a.Expression is BaseObjectCreationExpressionSyntax)) yield return Stripped(a.Expression);
                        yield break;
                    }
                    break;
            }
            if (one != null && !(one is InvocationExpressionSyntax || one is BaseObjectCreationExpressionSyntax)) yield return Stripped(one);
        }

        /// <summary>What was waited for, if a local: the values given it in its function. Null if it isn't a local.</summary>
        public static List<ExpressionSyntax> ValuesOf(ExpressionSyntax waited, SemanticModel model, SyntaxNode root)
        {
            if (!(model.GetSymbolInfo(waited).Symbol is ILocalSymbol local)) return null;
            var values = new List<ExpressionSyntax>();
            foreach (var x in root.DescendantNodes())
            {
                if (x is VariableDeclaratorSyntax v && v.Initializer != null && SymbolEqualityComparer.Default.Equals(model.GetDeclaredSymbol(v), local)) values.Add(v.Initializer.Value);
                if (x is AssignmentExpressionSyntax a && a.IsKind(SyntaxKind.SimpleAssignmentExpression) && SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(a.Left).Symbol, local)) values.Add(a.Right);
            }
            return values;
        }

        /// <summary>Why waiting for this might wait for any lock: it's a task the code was given, not one it made. Null if it made it.</summary>
        public static string Given(ExpressionSyntax waited, SemanticModel model, SyntaxNode root)
        {
            if (!(ValuesOf(waited, model, root) is List<ExpressionSyntax> values))
                return $"'{waited}', a task or thread it was given, which might be waiting for any lock";
            foreach (var v in values)
            {
                var e = Stripped(v);
                if (e is InvocationExpressionSyntax || e is BaseObjectCreationExpressionSyntax || e is AwaitExpressionSyntax || e is LiteralExpressionSyntax || e is DefaultExpressionSyntax) continue;
                if (model.GetSymbolInfo(e).Symbol is ILocalSymbol) continue;
                return $"'{waited}', which holds '{v}', a task or thread it was given, which might be waiting for any lock";
            }
            return null;
        }

        /// <summary>A walk over the code reachable from some, adding up what it takes.</summary>
        private sealed class Walk
        {
            private readonly LockLevels _owner;
            private readonly Summary _s;
            private readonly HashSet<(IMethodSymbol, bool)> _seen = new HashSet<(IMethodSymbol, bool)>();
            private readonly Stack<(IMethodSymbol m, bool onThis)> _work = new Stack<(IMethodSymbol, bool)>();

            public Walk(LockLevels owner, Summary s) { _owner = owner; _s = s; }

            public void Push(IMethodSymbol m, bool onThis, bool trustSaid = true)
            {
                m = m.OriginalDefinition;
                if (trustSaid && _owner.TakesNoLocks(m)) return;
                foreach (var b in _owner.Bodies(m))
                    if (_seen.Add((b, onThis))) _work.Push((b, onThis));
            }

            public void Run()
            {
                while (_work.Count > 0)
                {
                    var (m, onThis) = _work.Pop();
                    // (a wrapper takes its lock for its caller, where the form it is called in says so)
                    if (_owner._locks.Acquires(m) || _owner._locks.Releases(m)) continue;
                    foreach (var r in m.DeclaringSyntaxReferences)
                        Scan(r.GetSyntax(), _owner._compilation.GetSemanticModel(r.SyntaxTree), onThis, m);
                }
            }

            private static bool IntoSpec(SyntaxNode x, SemanticModel model) =>
                x is InvocationExpressionSyntax i && model.GetSymbolInfo(i).Symbol is IMethodSymbol m && (SpecSymbols.IsSpecClass(m.ContainingType) || i.Expression is IdentifierNameSyntax { Identifier: { Text: "nameof" } });

            public void Scan(SyntaxNode root, SemanticModel model, bool onThis, IMethodSymbol inMethod)
            {
                bool Into(SyntaxNode x) => x == root || !(x is AnonymousFunctionExpressionSyntax || x is LocalFunctionStatementSyntax || IntoSpec(x, model));
                foreach (var n in root.DescendantNodes(Into))
                {
                    if (n is AnonymousFunctionExpressionSyntax lambda)
                    {
                        if (RunsAtOnce(lambda, model)) Scan(lambda, model, onThis, inMethod);
                        continue;
                    }
                    if (n is LocalFunctionStatementSyntax || IntoSpec(n, model)) continue;
                    if (_owner.AcquiredAt(n, model) is Acquired a && a.Lock != null)
                        _s.Add(new Take { Lock = a.Lock, Element = a.Element, Semaphore = a.Semaphore, OnThis = onThis && (a.Receiver == "this" || a.Receiver == "static"), In = inMethod });
                    Call(n, model, onThis, inMethod, false);
                    foreach (var w in WaitedFor(n, model))
                        if (Given(w, model, root) is string why) _s.Unknown ??= why;
                }
            }

            /// <summary>What a node runs by calling, pushed to be walked; a lambda it runs at once is scanned as part of it, by whoever scans that.</summary>
            public void Call(SyntaxNode n, SemanticModel model, bool onThis, IMethodSymbol inMethod, bool lambdasToo)
            {
                switch (n)
                {
                    case InvocationExpressionSyntax inv when model.GetSymbolInfo(inv).Symbol is IMethodSymbol m:
                        if (IntoSpec(inv, model)) return;
                        if (m.MethodKind == MethodKind.DelegateInvoke)
                        {
                            if (!TakesNoLocks(m.ContainingType)) _s.Unknown ??= $"'{inv.Expression}', a delegate that might take any lock";
                            return;
                        }
                        if (_owner._locks.Acquires(m) || _owner._locks.Releases(m)) return;
                        if (m.DeclaringSyntaxReferences.Length > 0 || Engine.IsOverridable(m) && _owner.Bodies(m).Any())
                        {
                            bool onIt = !m.IsStatic && (inv.Expression is SimpleNameSyntax || inv.Expression is MemberAccessExpressionSyntax ma && (ma.Expression is ThisExpressionSyntax || ma.Expression is BaseExpressionSyntax));
                            Push(m, onThis && onIt);
                        }
                        // (what a library call runs: the methods and delegates given it)
                        if (m.DeclaringSyntaxReferences.Length == 0 && !Starters.Contains(m.Name))
                            foreach (var arg in inv.ArgumentList.Arguments)
                            {
                                if (arg.Expression is AnonymousFunctionExpressionSyntax lambda)
                                {
                                    // (when the walk starts at this call, its lambdas are part of it; in a scan, the scan finds them)
                                    if (lambdasToo) Scan(lambda, model, onThis, inMethod);
                                    continue;
                                }
                                if (!(model.GetTypeInfo(arg.Expression).ConvertedType is INamedTypeSymbol dt) || dt.TypeKind != TypeKind.Delegate || TakesNoLocks(dt)) continue;
                                if (model.GetSymbolInfo(arg.Expression).Symbol is IMethodSymbol group) Push(group, false);
                                else if (!(arg.Expression is LiteralExpressionSyntax)) _s.Unknown ??= $"'{arg.Expression}', a delegate given to '{m.Name}', which might take any lock";
                            }
                        return;
                    case BaseObjectCreationExpressionSyntax c when model.GetSymbolInfo(c).Symbol is IMethodSymbol ctor && ctor.DeclaringSyntaxReferences.Length > 0:
                        Push(ctor, false);
                        return;
                    case SimpleNameSyntax name when model.GetSymbolInfo(name).Symbol is IPropertySymbol p && !(name.Parent is NameColonSyntax || name.Parent is NameEqualsSyntax):
                        Accessors(p, LockGuards.IsWriteTarget(name), !(name.Parent is MemberAccessExpressionSyntax pm && pm.Name == name) || ((MemberAccessExpressionSyntax)name.Parent).Expression is ThisExpressionSyntax, onThis);
                        return;
                    case ElementAccessExpressionSyntax ea when model.GetSymbolInfo(ea).Symbol is IPropertySymbol ip:
                        Accessors(ip, LockGuards.IsWriteTarget(ea), ea.Expression is ThisExpressionSyntax, onThis);
                        return;
                }
            }

            private void Accessors(IPropertySymbol p, bool written, bool onIt, bool onThis)
            {
                bool both = written; // (x.P += 1 reads it too; a plain write may as well count both)
                if (p.GetMethod != null && (!written || both)) Push(p.GetMethod, onThis && onIt && !p.IsStatic);
                if (p.SetMethod != null && written) Push(p.SetMethod, onThis && onIt && !p.IsStatic);
            }
        }
    }
}
