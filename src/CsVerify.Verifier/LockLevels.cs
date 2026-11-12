using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// The order locks are taken in (Chalice's and Viper's lock levels, Clang's ACQUIRED_AFTER): a lock's
    /// <c>[LockLevel]</c>, on its field or its class, and what locks code may take or wait for, by itself or through what it
    /// calls, including what a library calls back. A thread that takes locks only in increasing order of level, and waits
    /// for nothing that might need a lock it holds, can't be part of a cycle of threads waiting on each other. So a lock
    /// taken, a call made, or a task waited for while a lock is held must take only higher locks (CSV1025; see
    /// StaticChecks.LockLevels).
    /// </summary>
    internal sealed class LockLevels
    {
        private readonly Compilation _compilation;
        private readonly LockGuards _locks;
        private readonly IReadOnlyList<INamedTypeSymbol> _types;
        private readonly Dictionary<IMethodSymbol, Summary> _memo = new Dictionary<IMethodSymbol, Summary>(SymbolEqualityComparer.Default);
        private readonly Dictionary<ITypeSymbol, List<IMethodSymbol>> _callbacks = new Dictionary<ITypeSymbol, List<IMethodSymbol>>(SymbolEqualityComparer.Default);
        private readonly HashSet<SyntaxNode> _claimed = new HashSet<SyntaxNode>();
        private List<(SyntaxNode at, string message)> _misdeclared;

        public LockLevels(Compilation compilation, LockGuards locks, IReadOnlyList<INamedTypeSymbol> types)
        {
            _compilation = compilation;
            _locks = locks;
            _types = types;
        }

        /// <summary>
        /// Whose lock a taken lock is, from where the code taking it is called: the receiver (Index -1) or an argument of the
        /// call the walk started at (AtCall), or this (-1) or a parameter of the method it started in.
        /// </summary>
        public readonly record struct Origin(bool AtCall, int Index);

        /// <summary>A lock code takes: its field or class (or the array whose element it is), whose it is if that can be told, and the method that takes it.</summary>
        public sealed class Take
        {
            public ISymbol Lock;
            public bool Element, Semaphore;
            public Origin? Origin;
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
                if (!Taken.Any(x => SymbolEqualityComparer.Default.Equals(x.Lock, t.Lock) && x.Element == t.Element && Equals(x.Origin, t.Origin))) Taken.Add(t);
            }
        }

        /// <summary>
        /// A lock taken at a point of the code: what it is a lock of (a field, an array, or a class whose objects are
        /// locked), whose (the expression of the object, null for this), and as written ("this", "static", or the expression).
        /// </summary>
        public sealed class Acquired
        {
            public ISymbol Lock;
            public bool Element, Semaphore, Static, Formless;
            public ExpressionSyntax Owner;
            public string Receiver;
            public SyntaxNode At, Expression;
        }

        private static AttributeData LevelAttribute(ISymbol s) => s?.GetAttributes().FirstOrDefault(a => a.AttributeClass?.Name == "LockLevelAttribute");

        /// <summary>The class whose [LockLevel] its objects' locks have: the type or its nearest base that says one. Null if none does.</summary>
        public static INamedTypeSymbol LeveledClass(ITypeSymbol t)
        {
            for (var b = t as INamedTypeSymbol; b != null; b = b.BaseType)
                if (LevelAttribute(b.OriginalDefinition) != null) return b.OriginalDefinition;
            return null;
        }

        public static int? Level(ISymbol lockSymbol) =>
            (lockSymbol is IFieldSymbol || lockSymbol is INamedTypeSymbol) && LevelAttribute(lockSymbol) is AttributeData a && a.ConstructorArguments.FirstOrDefault().Value is int n ? n : (int?)null;

        /// <summary>The readonly int field two locks of this lock on different objects are ordered by, or null.</summary>
        public static IFieldSymbol OrderedBy(ISymbol lockSymbol)
        {
            if (!(LevelAttribute(lockSymbol) is AttributeData a) || !(a.NamedArguments.FirstOrDefault(x => x.Key == "OrderedBy").Value.Value is string named)) return null;
            var owner = lockSymbol is IFieldSymbol f ? f.ContainingType : lockSymbol as INamedTypeSymbol;
            for (var t = owner; t != null; t = t.BaseType)
                if (t.GetMembers(named).OfType<IFieldSymbol>().FirstOrDefault(k => k.Type.SpecialType == SpecialType.System_Int32 || k.Type.SpecialType == SpecialType.System_Int64) is IFieldSymbol key) return key;
            return null;
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

        /// <summary>Report each of these once, by whoever gets to it.</summary>
        public bool Claim(SyntaxNode at) => _claimed.Add(at);

        /// <summary>
        /// Levels that could let one object be two locks of different levels, which would undo the order: a class that
        /// says one when a base class does, a field that says one when its objects' class does, and a leveled lock field
        /// that isn't readonly or is given anything but a new object.
        /// </summary>
        public IReadOnlyList<(SyntaxNode at, string message)> Misdeclared()
        {
            if (_misdeclared != null) return _misdeclared;
            _misdeclared = new List<(SyntaxNode, string)>();
            foreach (var t in _types)
            {
                if (LevelAttribute(t) != null && t.BaseType != null && LeveledClass(t.BaseType) is INamedTypeSymbol b && t.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is SyntaxNode td)
                    _misdeclared.Add((td, $"'{t.Name}' says [LockLevel], but '{b.Name}' already does: one object would be two locks of different levels"));
                foreach (var f in t.GetMembers().OfType<IFieldSymbol>())
                {
                    if (LevelAttribute(f) == null || !(f.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is VariableDeclaratorSyntax v)) continue;
                    if (LeveledClass(f.Type) is INamedTypeSymbol c) { _misdeclared.Add((v, $"'{f.Name}' says [LockLevel], but its objects' class '{c.Name}' already does")); continue; }
                    if (f.Type.IsValueType) continue; // (a SpinLock: the field is the lock itself)
                    if (!f.IsReadOnly) { _misdeclared.Add((v, $"'{f.Name}' has a lock level, but isn't readonly: threads could lock different objects by it")); continue; }
                    var model = _compilation.GetSemanticModel(v.SyntaxTree);
                    var given = new List<ExpressionSyntax>();
                    if (v.Initializer != null) given.Add(v.Initializer.Value);
                    foreach (var r in t.DeclaringSyntaxReferences)
                        foreach (var a in r.GetSyntax().DescendantNodes().OfType<AssignmentExpressionSyntax>())
                            if (SymbolEqualityComparer.Default.Equals(model.SyntaxTree == a.SyntaxTree ? model.GetSymbolInfo(a.Left).Symbol : _compilation.GetSemanticModel(a.SyntaxTree).GetSymbolInfo(a.Left).Symbol, f))
                                given.Add(a.Right);
                    if (f.Type is IArrayTypeSymbol) continue; // (an array's elements are its locks, ordered by index)
                    if (given.Any(g => !(g is BaseObjectCreationExpressionSyntax)))
                        _misdeclared.Add((v, $"'{f.Name}' has a lock level, so it must be given a new object of its own: another lock's object would be two locks of different levels"));
                }
            }
            return _misdeclared;
        }

        // ---- where locks are taken, and held ----

        private static ExpressionSyntax Bare(ExpressionSyntax e)
        {
            while (e is ParenthesizedExpressionSyntax p) e = p.Expression;
            return e;
        }

        /// <summary>
        /// What a lock statement's expression locks: a field; an array's element; an object of a class with a level (this,
        /// a parameter, a field of that type); a local that only ever holds one of those. Otherwise the symbol is the
        /// expression's class, or null for object or an interface: no level can be had.
        /// </summary>
        public (ISymbol sym, bool element, ExpressionSyntax owner, string receiver, bool isStatic) LockTarget(ExpressionSyntax e, SemanticModel model)
        {
            e = Bare(e);
            if (e is ElementAccessExpressionSyntax ea) return (model.GetSymbolInfo(ea.Expression).Symbol, true, ea.Expression, ea.Expression.ToString(), false);
            var s = model.GetSymbolInfo(e).Symbol;
            if (s is IFieldSymbol f && LeveledClass(f.Type) == null)
            {
                var owner = e is MemberAccessExpressionSyntax ma && !(ma.Expression is ThisExpressionSyntax) ? ma.Expression : null;
                return (f, false, f.IsStatic ? null : owner, f.IsStatic ? "static" : owner?.ToString() ?? "this", f.IsStatic);
            }
            // (a local that is given one lock and never another: that lock)
            if (s is ILocalSymbol local && local.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is VariableDeclaratorSyntax v && v.Initializer != null &&
                !v.Ancestors().OfType<BlockSyntax>().Last().DescendantNodes().OfType<AssignmentExpressionSyntax>().Any(a => SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(a.Left).Symbol, local)) &&
                !(Bare(v.Initializer.Value) is BaseObjectCreationExpressionSyntax))
                return LockTarget(v.Initializer.Value, model);
            var type = model.GetTypeInfo(e).Type;
            if (type == null || type.TypeKind != TypeKind.Class || type.SpecialType == SpecialType.System_Object || e is TypeOfExpressionSyntax)
                return (null, false, e, e.ToString(), false);
            var cls = LeveledClass(type) ?? (INamedTypeSymbol)type.OriginalDefinition;
            bool isStatic = s is IFieldSymbol sf && sf.IsStatic;
            return (cls, false, e, e is ThisExpressionSyntax ? "this" : e.ToString(), isStatic);
        }

        /// <summary>The expression of the object whose semaphore a taking statement or using is about; null for this.</summary>
        private ExpressionSyntax GateOwner(SyntaxNode at, IFieldSymbol gate, SemanticModel model)
        {
            foreach (var name in at.DescendantNodesAndSelf().OfType<SimpleNameSyntax>())
                if (SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(name).Symbol, gate))
                    return name.Parent is MemberAccessExpressionSyntax ma && ma.Name == name && !(ma.Expression is ThisExpressionSyntax) ? ma.Expression : null;
            foreach (var inv in at.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>())
                if (SymbolEqualityComparer.Default.Equals(_locks.GateOfWrapper(inv, model, true), gate) && inv.Expression is MemberAccessExpressionSyntax wm && !(wm.Expression is ThisExpressionSyntax))
                    return wm.Expression;
            return null;
        }

        private Acquired Gate(IFieldSymbol gate, SyntaxNode at, SyntaxNode around, SemanticModel model)
        {
            var owner = gate.IsStatic ? null : GateOwner(around, gate, model);
            return new Acquired { Lock = gate, Semaphore = true, Static = gate.IsStatic, Owner = owner, Receiver = gate.IsStatic ? "static" : owner?.ToString() ?? "this", At = at, Expression = at };
        }

        /// <summary>The lock this node takes, if it is a lock statement, the statement that takes a semaphore before its try, or a using that holds one.</summary>
        public Acquired AcquiredAt(SyntaxNode n, SemanticModel model)
        {
            switch (n)
            {
                case LockStatementSyntax l:
                    var (sym, element, owner, receiver, isStatic) = LockTarget(l.Expression, model);
                    return new Acquired { Lock = sym, Element = element, Owner = owner, Receiver = receiver, Static = isStatic, At = l, Expression = l.Expression };
                case StatementSyntax st when LockGuards.TryAfter(st) is TryStatementSyntax t && _locks.GateOfTry(t, model) is IFieldSymbol gate && _locks.IsMutexGate(gate):
                    return Gate(gate, st, st, model);
                // (a flag taken as a try-lock never waits: it can't be part of a deadlock)
                case StatementSyntax fs when LockGuards.PrimitiveTaken(fs, model)?.kind == "Flag":
                    return null;
                case StatementSyntax ps when LockGuards.PrimitiveTaken(ps, model) is var (lockExpr, kind):
                    var (psym, pel, powner, preceiver, pstatic) = LockTarget(lockExpr, model);
                    // (a SpinLock isn't reentrant: taken again, it waits for itself)
                    return new Acquired { Lock = psym, Element = pel, Owner = powner, Receiver = preceiver, Static = pstatic, Semaphore = kind == "SpinLock", At = ps, Expression = lockExpr,
                                          Formless = LockGuards.PrimitiveTryOf(ps, model) == null };
                case UsingStatementSyntax u when _locks.GateOfUsing(u, model) is IFieldSymbol g:
                    return Gate(g, u, (SyntaxNode)u.Expression ?? u.Declaration, model);
                case LocalDeclarationStatementSyntax d when _locks.GateOfUsing(d, model) is IFieldSymbol g2:
                    return Gate(g2, d, d.Declaration, model);
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
                    case TryStatementSyntax pt when LockGuards.PrimitiveForm(pt, model) is { } form && form.held.Any(h => h.Span.Contains(n.Span)):
                        if (AcquiredAt(form.taking, model) is Acquired ap) yield return ap;
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

        private static Origin?[] Own(IMethodSymbol m, bool atCall) =>
            new Origin?[] { new Origin(atCall, -1) }.Concat(m.Parameters.Select(p => (Origin?)new Origin(atCall, p.Ordinal))).ToArray();

        /// <summary>The locks a method may take, by itself and through what it calls and waits for. Origins are of its own this and parameters.</summary>
        public Summary Of(IMethodSymbol m)
        {
            m = m.OriginalDefinition;
            if (_memo.TryGetValue(m, out var known)) return known;
            var s = new Summary();
            var work = new Walk(this, s);
            work.Push(m, Own(m, false));
            work.Run();
            return _memo[m] = s;
        }

        /// <summary>What a method's own body may take, even if it says it takes none (to check that it doesn't).</summary>
        public Summary OfBody(IMethodSymbol m)
        {
            var s = new Summary();
            var work = new Walk(this, s);
            work.Push(m, Own(m, false), trustSaid: false);
            work.Run();
            return s;
        }

        /// <summary>The locks a lambda (or other code) may take when it runs. Origins are of the method it is in.</summary>
        public Summary OfRegion(SyntaxNode region, SemanticModel model, IMethodSymbol inMethod)
        {
            var s = new Summary();
            var work = new Walk(this, s);
            work.Scan(region, model, Own(inMethod, false), inMethod);
            work.Run();
            return s;
        }

        /// <summary>
        /// What one node of code does by calling: the methods, accessors and lambdas it runs, and what they may take.
        /// Origins are the call's receiver and arguments (AtCall), and for the lambdas it runs, of the method it is in.
        /// </summary>
        public Summary OfCall(SyntaxNode node, SemanticModel model, IMethodSymbol inMethod)
        {
            var s = new Summary();
            var work = new Walk(this, s);
            work.Call(node, model, Own(inMethod, false), inMethod, lambdasToo: true, atCall: true);
            work.Run();
            return s;
        }

        /// <summary>What a node runs with no call written (an operator, a conversion, a foreach, a using, ...), and what that may take.</summary>
        public Summary OfImplicit(SyntaxNode node, SemanticModel model, IMethodSymbol inMethod)
        {
            var s = new Summary();
            var work = new Walk(this, s);
            work.Implicit(node, model, Own(inMethod, false), inMethod);
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
                    if (t.AllInterfaces.Any(i => SymbolEqualityComparer.Default.Equals(i.OriginalDefinition, m.ContainingType)))
                        foreach (var i in t.AllInterfaces.Where(i => SymbolEqualityComparer.Default.Equals(i.OriginalDefinition, m.ContainingType)))
                            if (i.GetMembers(m.Name).OfType<IMethodSymbol>().FirstOrDefault(x => SymbolEqualityComparer.Default.Equals(x.OriginalDefinition, m)) is IMethodSymbol im &&
                                t.FindImplementationForInterfaceMember(im) is IMethodSymbol impl && impl.DeclaringSyntaxReferences.Length > 0 && !impl.IsAbstract)
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

        /// <summary>
        /// What a library can call back on objects of a type it's handed: every override and interface implementation of
        /// the program's classes that can be one (all of them, for object, an interface or a type parameter).
        /// </summary>
        private List<IMethodSymbol> Callbacks(ITypeSymbol t)
        {
            if (t == null) return new List<IMethodSymbol>();
            if (_callbacks.TryGetValue(t, out var known)) return known;
            var list = new List<IMethodSymbol>();
            _callbacks[t] = list;
            if (t is IArrayTypeSymbol a) { list.AddRange(Callbacks(a.ElementType)); return list; }
            if (t is INamedTypeSymbol nt && nt.TypeArguments.Length > 0)
                foreach (var arg in nt.TypeArguments) list.AddRange(Callbacks(arg));
            bool any = t is ITypeParameterSymbol || t.SpecialType == SpecialType.System_Object || t.TypeKind == TypeKind.Interface || t.TypeKind == TypeKind.Delegate;
            foreach (var s in _types)
            {
                if (!(any ? t.TypeKind != TypeKind.Interface || s.AllInterfaces.Any(i => SymbolEqualityComparer.Default.Equals(i.OriginalDefinition, t.OriginalDefinition)) || t is ITypeParameterSymbol
                          : DataTypes.Derives(s, t))) continue;
                foreach (var m in s.GetMembers().OfType<IMethodSymbol>())
                {
                    if (m.DeclaringSyntaxReferences.Length == 0 || m.IsAbstract || m.IsStatic) continue;
                    bool overrides = m.IsOverride ||
                                     s.AllInterfaces.Any(i => i.GetMembers().OfType<IMethodSymbol>().Any(im => SymbolEqualityComparer.Default.Equals(s.FindImplementationForInterfaceMember(im), m)));
                    if (overrides) list.Add(m.OriginalDefinition);
                }
            }
            return list;
        }

        private static readonly HashSet<string> Starters = new HashSet<string> { "Run", "StartNew", "ContinueWith", "QueueUserWorkItem", "UnsafeQueueUserWorkItem" };

        /// <summary>A lambda given to a library call that runs it before returning (not one that starts it as a task or thread).</summary>
        private static bool RunsAtOnce(SyntaxNode lambda, SemanticModel model)
        {
            if (!(lambda.Parent is ArgumentSyntax arg) || !(arg.Parent?.Parent is InvocationExpressionSyntax inv)) return false;
            return model.GetSymbolInfo(inv).Symbol is IMethodSymbol m && !Starters.Contains(m.Name);
        }

        /// <summary>Is this lambda run where no synchronization context is: started on the thread pool?</summary>
        public static bool OnThePool(SyntaxNode n, SemanticModel model)
        {
            foreach (var lambda in n.AncestorsAndSelf().OfType<AnonymousFunctionExpressionSyntax>())
                if (lambda.Parent is ArgumentSyntax arg && arg.Parent?.Parent is InvocationExpressionSyntax inv && model.GetSymbolInfo(inv).Symbol is IMethodSymbol m &&
                    (m.Name == "Run" || m.Name == "StartNew" || m.Name == "QueueUserWorkItem") && m.DeclaringSyntaxReferences.Length == 0)
                    return true;
            return false;
        }

        public static ExpressionSyntax Stripped(ExpressionSyntax e)
        {
            if (e is InvocationExpressionSyntax ca && ca.Expression is MemberAccessExpressionSyntax cm && cm.Name.Identifier.Text == "ConfigureAwait") e = cm.Expression;
            return Bare(e);
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
            foreach (var (e, _) in Blocked(n, model))
                if (!(e is InvocationExpressionSyntax || e is BaseObjectCreationExpressionSyntax)) yield return e;
        }

        /// <summary>The tasks a node waits for, made there or not, and whether it blocks the thread for them (rather than awaiting). Not one already finished.</summary>
        public static IEnumerable<(ExpressionSyntax task, bool blocks)> Blocked(SyntaxNode n, SemanticModel model) =>
            BlockedAll(n, model).Where(x => !FinishedBefore(x.task, n, model));

        /// <summary>
        /// A local task already awaited by a statement that comes before this node in a block around it (so on every path
        /// here): <c>await t;</c> or <c>await Task.WhenAll(..., t, ...)</c>. Its Result doesn't wait.
        /// </summary>
        private static bool FinishedBefore(ExpressionSyntax task, SyntaxNode n, SemanticModel model)
        {
            if (!(model.GetSymbolInfo(task).Symbol is ILocalSymbol local)) return false;
            for (SyntaxNode inner = n, p = n.Parent; p != null && !(p is MemberDeclarationSyntax || p is AnonymousFunctionExpressionSyntax || p is LocalFunctionStatementSyntax); inner = p, p = p.Parent)
            {
                if (!(p is BlockSyntax b)) continue;
                foreach (var st in b.Statements.TakeWhile(x => x != inner))
                    foreach (var aw in st.DescendantNodesAndSelf(x => !(x is AnonymousFunctionExpressionSyntax || x is LocalFunctionStatementSyntax || x is IfStatementSyntax || x is TryStatementSyntax ||
                                                                         x is SwitchStatementSyntax || x is ConditionalExpressionSyntax || x is BinaryExpressionSyntax be && (be.IsKind(SyntaxKind.LogicalAndExpression) || be.IsKind(SyntaxKind.LogicalOrExpression) || be.IsKind(SyntaxKind.CoalesceExpression)) ||
                                                                         x is CommonForEachStatementSyntax || x is WhileStatementSyntax || x is ForStatementSyntax))
                                                .OfType<AwaitExpressionSyntax>())
                    {
                        var e = Stripped(aw.Expression);
                        var awaited = e is InvocationExpressionSyntax wa && wa.Expression is MemberAccessExpressionSyntax wm && wm.Name.Identifier.Text == "WhenAll"
                            ? wa.ArgumentList.Arguments.Select(a => Stripped(a.Expression)) : new[] { e };
                        if (awaited.Any(x => SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(x).Symbol, local))) return true;
                    }
            }
            return false;
        }

        private static IEnumerable<(ExpressionSyntax task, bool blocks)> BlockedAll(SyntaxNode n, SemanticModel model)
        {
            switch (n)
            {
                case AwaitExpressionSyntax aw:
                    yield return (Stripped(aw.Expression), false);
                    break;
                case MemberAccessExpressionSyntax ma when ma.Name.Identifier.Text == "Result" && IsWaitable(model.GetTypeInfo(ma.Expression).Type):
                    yield return (Stripped(ma.Expression), true);
                    break;
                case InvocationExpressionSyntax inv when inv.Expression is MemberAccessExpressionSyntax im:
                    var name = im.Name.Identifier.Text;
                    if ((name == "Wait" || name == "Join") && IsWaitable(model.GetTypeInfo(im.Expression).Type)) yield return (Stripped(im.Expression), true);
                    else if (name == "GetResult" && im.Expression is InvocationExpressionSyntax ga && ga.Expression is MemberAccessExpressionSyntax gm && gm.Name.Identifier.Text == "GetAwaiter")
                        yield return (Stripped(gm.Expression), true);
                    else if ((name == "WhenAll" || name == "WhenAny" || name == "WaitAll" || name == "WaitAny") && model.GetSymbolInfo(inv).Symbol is IMethodSymbol wm && wm.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task")
                        foreach (var a in inv.ArgumentList.Arguments)
                            yield return (Stripped(a.Expression), name.StartsWith("Wait"));
                    break;
            }
        }

        private static readonly HashSet<string> Primitives = new HashSet<string>
        {
            "System.Threading.WaitHandle", "System.Threading.EventWaitHandle", "System.Threading.ManualResetEvent", "System.Threading.AutoResetEvent",
            "System.Threading.Mutex", "System.Threading.Semaphore", "System.Threading.ManualResetEventSlim", "System.Threading.SemaphoreSlim",
            "System.Threading.CountdownEvent", "System.Threading.Barrier",
        };

        /// <summary>
        /// A wait on something only another thread can end, other than a lock in its form or a task: an event, a
        /// semaphore that isn't a lock, a countdown, a barrier, a monitor's Wait. Why, or null.
        /// </summary>
        public string Blocking(SyntaxNode n, SemanticModel model)
        {
            if (!(n is InvocationExpressionSyntax inv) || !(model.GetSymbolInfo(inv).Symbol is IMethodSymbol m) || m.ContainingType == null) return null;
            var type = m.ContainingType.OriginalDefinition.ToDisplayString();
            if (type == "System.Threading.Monitor" && m.Name == "Wait") return $"'{inv}', which waits until another thread pulses it";
            if (!Primitives.Contains(type) || !(m.Name.StartsWith("Wait") || m.Name == "SignalAndWait")) return null;
            // (a semaphore of count 1 taken in its form is a lock, with a level of its own)
            if (inv.FirstAncestorOrSelf<StatementSyntax>() is StatementSyntax st && AcquiredAt(st, model) is Acquired a && !a.Formless) return null;
            return $"'{inv}', which waits until another thread signals it";
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

        // ---- a synchronization context: blocking on code that comes back to it ----

        /// <summary>
        /// An await in this async method, or in an async method of the program it calls, that resumes on the context it
        /// started on (no ConfigureAwait(false)). Blocking on the method from that context would wait for itself. Null if none.
        /// </summary>
        public SyntaxNode KeepsContext(IMethodSymbol m)
        {
            var seen = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
            var work = new Stack<IMethodSymbol>();
            void Push(IMethodSymbol x) { foreach (var b in Bodies(x)) if (b.IsAsync && seen.Add(b)) work.Push(b); }
            Push(m);
            while (work.Count > 0)
            {
                var x = work.Pop();
                foreach (var r in x.DeclaringSyntaxReferences)
                {
                    var model = _compilation.GetSemanticModel(r.SyntaxTree);
                    var body = r.GetSyntax();
                    bool Own(SyntaxNode y) => y == body || !(y is AnonymousFunctionExpressionSyntax || y is LocalFunctionStatementSyntax);
                    foreach (var n in body.DescendantNodes(Own))
                    {
                        switch (n)
                        {
                            case AwaitExpressionSyntax aw when !FreeOfContext(aw.Expression):
                                return aw;
                            case ForEachStatementSyntax fe when !fe.AwaitKeyword.IsKind(SyntaxKind.None) && !FreeOfContext(fe.Expression):
                                return fe;
                            case UsingStatementSyntax us when !us.AwaitKeyword.IsKind(SyntaxKind.None):
                                return us;
                            case LocalDeclarationStatementSyntax ld when !ld.AwaitKeyword.IsKind(SyntaxKind.None):
                                return ld;
                            case InvocationExpressionSyntax call when model.GetSymbolInfo(call).Symbol is IMethodSymbol callee:
                                Push(callee);
                                break;
                        }
                    }
                }
            }
            return null;
        }

        private static bool FreeOfContext(ExpressionSyntax e) =>
            Bare(e) is InvocationExpressionSyntax ca && ca.Expression is MemberAccessExpressionSyntax cm && cm.Name.Identifier.Text == "ConfigureAwait" &&
            ca.ArgumentList.Arguments.Count == 1 && ca.ArgumentList.Arguments[0].Expression.IsKind(SyntaxKind.FalseLiteralExpression);

        /// <summary>A walk over the code reachable from some, adding up what it takes.</summary>
        private sealed class Walk
        {
            private readonly LockLevels _owner;
            private readonly Summary _s;
            private readonly HashSet<string> _seen = new HashSet<string>();
            private readonly Dictionary<IMethodSymbol, int> _variants = new Dictionary<IMethodSymbol, int>(SymbolEqualityComparer.Default);
            private readonly Stack<(IMethodSymbol m, Origin?[] map)> _work = new Stack<(IMethodSymbol, Origin?[])>();

            public Walk(LockLevels owner, Summary s) { _owner = owner; _s = s; }

            /// <summary>A method to walk, with whose its this and parameters are (null where that can't be told).</summary>
            public void Push(IMethodSymbol m, Origin?[] map, bool trustSaid = true)
            {
                m = m.OriginalDefinition;
                if (trustSaid && _owner.TakesNoLocks(m)) return;
                foreach (var b in _owner.Bodies(m))
                {
                    var bm = map ?? new Origin?[b.Parameters.Length + 1];
                    // (the same method from many places: past a few, whose it is is forgotten)
                    _variants.TryGetValue(b, out var count);
                    if (count >= 6) bm = new Origin?[b.Parameters.Length + 1];
                    var key = (b.GetDocumentationCommentId() ?? b.ToDisplayString()) + "|" + string.Join(",", bm.Select(o => o?.ToString() ?? "_"));
                    if (!_seen.Add(key)) continue;
                    _variants[b] = count + 1;
                    _work.Push((b, bm));
                }
            }

            public void Run()
            {
                while (_work.Count > 0)
                {
                    var (m, map) = _work.Pop();
                    // (a wrapper takes its lock for its caller, where the form it is called in says so)
                    if (_owner._locks.Acquires(m) || _owner._locks.Releases(m)) continue;
                    foreach (var r in m.DeclaringSyntaxReferences)
                        Scan(r.GetSyntax(), _owner._compilation.GetSemanticModel(r.SyntaxTree), map, m);
                }
            }

            private static bool IntoSpec(SyntaxNode x, SemanticModel model) =>
                x is InvocationExpressionSyntax i && model.GetSymbolInfo(i).Symbol is IMethodSymbol m && (SpecSymbols.IsSpecClass(m.ContainingType) || i.Expression is IdentifierNameSyntax { Identifier: { Text: "nameof" } });

            private static Origin? At(Origin?[] map, int i) => map != null && i >= 0 && i < map.Length ? map[i] : null;

            /// <summary>Whose an operation's value is, in terms of the map: this, or a parameter of the method being walked.</summary>
            private static Origin? OriginOf(IOperation op, Origin?[] map, IMethodSymbol inMethod)
            {
                while (op is IConversionOperation c && c.IsImplicit || op is IParenthesizedOperation) op = op is IConversionOperation cc ? cc.Operand : ((IParenthesizedOperation)op).Operand;
                switch (op)
                {
                    case null: return At(map, 0);
                    case IInstanceReferenceOperation _: return At(map, 0);
                    case IParameterReferenceOperation p when SymbolEqualityComparer.Default.Equals(p.Parameter.ContainingSymbol?.OriginalDefinition, inMethod?.OriginalDefinition):
                        return At(map, p.Parameter.Ordinal + 1);
                }
                return null;
            }

            private static Origin? OriginOfSyntax(ExpressionSyntax e, SemanticModel model, Origin?[] map, IMethodSymbol inMethod) =>
                e == null ? At(map, 0) : OriginOf(model.GetOperation(e), map, inMethod);

            /// <summary>Where a callee's this and parameters come from, at this call.</summary>
            private static Origin?[] MapAt(IMethodSymbol callee, IOperation instance, IEnumerable<IArgumentOperation> args, Origin?[] map, IMethodSymbol inMethod, bool atCall)
            {
                var result = new Origin?[callee.Parameters.Length + 1];
                result[0] = callee.IsStatic ? null : atCall ? new Origin(true, -1) : instance == null && callee.MethodKind != MethodKind.Constructor ? At(map, 0) : instance == null ? null : OriginOf(instance, map, inMethod);
                foreach (var a in args ?? Enumerable.Empty<IArgumentOperation>())
                    if (a.Parameter != null && a.Parameter.Ordinal + 1 < result.Length)
                        result[a.Parameter.Ordinal + 1] = atCall ? new Origin(true, a.Parameter.Ordinal) : OriginOf(a.Value, map, inMethod);
                return result;
            }

            public void Scan(SyntaxNode root, SemanticModel model, Origin?[] map, IMethodSymbol inMethod)
            {
                bool Into(SyntaxNode x) => x == root || !(x is AnonymousFunctionExpressionSyntax || x is LocalFunctionStatementSyntax || IntoSpec(x, model));
                foreach (var n in root.DescendantNodes(Into))
                {
                    if (n is AnonymousFunctionExpressionSyntax lambda)
                    {
                        if (RunsAtOnce(lambda, model)) Scan(lambda, model, map, inMethod);
                        continue;
                    }
                    if (n is LocalFunctionStatementSyntax || IntoSpec(n, model)) continue;
                    if (_owner.AcquiredAt(n, model) is Acquired a && a.Lock != null)
                        _s.Add(new Take { Lock = a.Lock, Element = a.Element, Semaphore = a.Semaphore, Origin = a.Static ? null : OriginOfSyntax(a.Owner, model, map, inMethod), In = inMethod });
                    else if (n is LockStatementSyntax unknownLock)
                        _s.Unknown ??= $"'lock ({unknownLock.Expression})', a lock on an object of no class with a level";
                    Call(n, model, map, inMethod, lambdasToo: false, atCall: false);
                    Implicit(n, model, map, inMethod);
                    foreach (var w in WaitedFor(n, model))
                        if (Given(w, model, root) is string why) _s.Unknown ??= why;
                    if (_owner.Blocking(n, model) is string blocks) _s.Unknown ??= blocks;
                }
            }

            /// <summary>Calls with no call written: operators, conversions, foreach, using, events, initializers' Add, property patterns.</summary>
            public void Implicit(SyntaxNode n, SemanticModel model, Origin?[] map, IMethodSymbol inMethod)
            {
                if (!(n is ExpressionSyntax || n is StatementSyntax || n is SubpatternSyntax)) return;
                var op = model.GetOperation(n);
                if (op == null) return;
                void Run(IMethodSymbol m) { if (m != null && (m.DeclaringSyntaxReferences.Length > 0 || Engine.IsOverridable(m))) Push(m, null); }
                switch (op)
                {
                    case IBinaryOperation b: Run(b.OperatorMethod); break;
                    case IUnaryOperation u: Run(u.OperatorMethod); break;
                    case IIncrementOrDecrementOperation i: Run(i.OperatorMethod); break;
                    case ICompoundAssignmentOperation ca: Run(ca.OperatorMethod); break;
                    case IConversionOperation c: Run(c.OperatorMethod); break;
                    case IEventAssignmentOperation ea when ea.EventReference is IEventReferenceOperation er: Run(ea.Adds ? er.Event.AddMethod : er.Event.RemoveMethod); break;
                    case IForEachLoopOperation fe:
                        if (model.GetForEachStatementInfo((CommonForEachStatementSyntax)n) is var info)
                        {
                            Run(info.GetEnumeratorMethod); Run(info.MoveNextMethod); Run(info.CurrentProperty?.GetMethod); Run(info.DisposeMethod);
                        }
                        break;
                    case IUsingOperation us:
                        var types = us.Resources is IVariableDeclarationGroupOperation g ? g.Declarations.SelectMany(x => x.Declarators).Select(x => x.Symbol.Type) : new[] { us.Resources?.Type };
                        foreach (var rt in types.Where(x => x != null))
                        {
                            Run(rt.GetMembers("Dispose").OfType<IMethodSymbol>().FirstOrDefault(x => x.Parameters.Length == 0));
                            Run(rt.GetMembers("DisposeAsync").OfType<IMethodSymbol>().FirstOrDefault(x => x.Parameters.Length == 0));
                        }
                        break;
                    case IUsingDeclarationOperation ud:
                        foreach (var d in ud.DeclarationGroup.Declarations.SelectMany(x => x.Declarators))
                            if (d.Symbol.Type is ITypeSymbol dt)
                            {
                                Run(dt.GetMembers("Dispose").OfType<IMethodSymbol>().FirstOrDefault(x => x.Parameters.Length == 0));
                                Run(dt.GetMembers("DisposeAsync").OfType<IMethodSymbol>().FirstOrDefault(x => x.Parameters.Length == 0));
                            }
                        break;
                    case IObjectOrCollectionInitializerOperation init:
                        foreach (var add in init.Initializers.OfType<IInvocationOperation>()) Run(add.TargetMethod);
                        break;
                    case IPropertySubpatternOperation ps when ps.Member is IPropertyReferenceOperation pr:
                        Run(pr.Property.GetMethod);
                        break;
                }
            }

            /// <summary>
            /// What a node runs by calling, pushed to be walked; a lambda it runs at once is scanned as part of it, by whoever
            /// scans that. A library call also runs what it can call back on what it's given.
            /// </summary>
            public void Call(SyntaxNode n, SemanticModel model, Origin?[] map, IMethodSymbol inMethod, bool lambdasToo, bool atCall)
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
                        var op = model.GetOperation(inv) as IInvocationOperation;
                        if (m.DeclaringSyntaxReferences.Length > 0 || Engine.IsOverridable(m) && _owner.Bodies(m).Any())
                            Push(m, MapAt(m, op?.Instance, op?.Arguments, map, inMethod, atCall));
                        if (m.DeclaringSyntaxReferences.Length > 0) return;
                        // (what a library call runs: the methods and delegates given it, and what it can call back on what it's given)
                        // (the threading primitives call nothing back)
                        var ns = m.ContainingNamespace?.ToDisplayString();
                        if (op != null && ns != "System.Threading" && ns != "System.Threading.Tasks")
                        {
                            foreach (var t in m.ContainingType.TypeArguments.Concat(m.TypeArguments)) CallBack(t);
                            if (!m.IsStatic && op.Instance != null) CallBack(Handed(op.Instance));
                            foreach (var a in op.Arguments.Where(a => a.Parameter?.Type.TypeKind != TypeKind.Delegate)) CallBack(Handed(a.Value));
                        }
                        if (Starters.Contains(m.Name)) return;
                        foreach (var arg in inv.ArgumentList.Arguments)
                        {
                            if (arg.Expression is AnonymousFunctionExpressionSyntax lambda)
                            {
                                // (when the walk starts at this call, its lambdas are part of it; in a scan, the scan finds them)
                                if (lambdasToo) Scan(lambda, model, map, inMethod);
                                continue;
                            }
                            if (!(model.GetTypeInfo(arg.Expression).ConvertedType is INamedTypeSymbol dt) || dt.TypeKind != TypeKind.Delegate || TakesNoLocks(dt)) continue;
                            if (model.GetSymbolInfo(arg.Expression).Symbol is IMethodSymbol group) Push(group, null);
                            else if (!(arg.Expression is LiteralExpressionSyntax)) _s.Unknown ??= $"'{arg.Expression}', a delegate given to '{m.Name}', which might take any lock";
                        }
                        return;
                    case BaseObjectCreationExpressionSyntax c when model.GetSymbolInfo(c).Symbol is IMethodSymbol ctor:
                        var co = model.GetOperation(c) as IObjectCreationOperation;
                        if (ctor.DeclaringSyntaxReferences.Length > 0) { Push(ctor, MapAt(ctor, null, co?.Arguments, map, inMethod, false)); return; }
                        if (co != null)
                        {
                            foreach (var t in ctor.ContainingType.TypeArguments) CallBack(t);
                            foreach (var a in co.Arguments.Where(a => a.Parameter?.Type.TypeKind != TypeKind.Delegate)) CallBack(Handed(a.Value));
                        }
                        return;
                    case SimpleNameSyntax name when model.GetSymbolInfo(name).Symbol is IPropertySymbol p && !(name.Parent is NameColonSyntax || name.Parent is NameEqualsSyntax):
                        var pe = (ExpressionSyntax)(name.Parent is MemberAccessExpressionSyntax pm && pm.Name == name ? pm : name);
                        Accessors(p, LockGuards.IsWriteTarget(name), model.GetOperation(pe) as IPropertyReferenceOperation, map, inMethod, atCall);
                        return;
                    case ElementAccessExpressionSyntax ea when model.GetSymbolInfo(ea).Symbol is IPropertySymbol ip:
                        Accessors(ip, LockGuards.IsWriteTarget(ea), model.GetOperation(ea) as IPropertyReferenceOperation, map, inMethod, atCall);
                        return;
                }
            }

            private void CallBack(ITypeSymbol t)
            {
                foreach (var m in _owner.Callbacks(t)) Push(m, null);
                // (a collection made with a comparer calls it later: whatever compares or hashes what it holds)
                if (t is INamedTypeSymbol nt)
                    foreach (var arg in nt.TypeArguments)
                        foreach (var s in _owner._types)
                            if (s.AllInterfaces.Any(i => (i.Name == "IEqualityComparer" || i.Name == "IComparer") && i.TypeArguments.Any(x => SymbolEqualityComparer.Default.Equals(x, arg))))
                                foreach (var cm in _owner.Callbacks(s)) Push(cm, null);
            }

            /// <summary>The type of what is handed over: under implicit reference conversions (to object, to a base class).</summary>
            private static ITypeSymbol Handed(IOperation op)
            {
                while (op is IConversionOperation c && c.IsImplicit && c.Operand.Type != null) op = c.Operand;
                return op?.Type;
            }

            private void Accessors(IPropertySymbol p, bool written, IPropertyReferenceOperation op, Origin?[] map, IMethodSymbol inMethod, bool atCall)
            {
                // (x.P += 1 reads it too; a plain write may as well count both)
                if (p.GetMethod != null) Push(p.GetMethod, MapAt(p.GetMethod, op?.Instance, op?.Arguments, map, inMethod, atCall));
                if (p.SetMethod != null && written) Push(p.SetMethod, MapAt(p.SetMethod, op?.Instance, op?.Arguments, map, inMethod, atCall));
            }
        }
    }
}
