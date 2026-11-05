using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using Microsoft.CodeAnalysis;

namespace CsVerify.Analyzers
{
    /// <summary>
    /// The [ContractsFor] stubs of a compilation: which stub method specifies which external member, and the [Model]
    /// functions. Stubs are found in the sources and in the CsVerify assembly (its BCL contracts); a stub in the
    /// sources wins over the CsVerify assembly's for the same member.
    /// </summary>
    public sealed class ContractStubs
    {
        private readonly Dictionary<IMethodSymbol, IMethodSymbol> _stubOf = new Dictionary<IMethodSymbol, IMethodSymbol>(SymbolEqualityComparer.Default);
        private readonly HashSet<IMethodSymbol> _stubs = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
        private readonly Dictionary<IMethodSymbol, IMethodSymbol> _queryOf = new Dictionary<IMethodSymbol, IMethodSymbol>(SymbolEqualityComparer.Default);

        /// <summary>The [Model] functions, in a fixed order.</summary>
        public readonly IReadOnlyList<IMethodSymbol> Models;

        /// <summary>The library types a [MustDispose] stub class marks (FileStream): their objects must be disposed.</summary>
        public readonly HashSet<INamedTypeSymbol> MustDisposeTargets = new HashSet<INamedTypeSymbol>(SymbolEqualityComparer.Default);

        /// <summary>Stub methods that match no member of their type, or are not well-formed, and why.</summary>
        public readonly IReadOnlyList<(IMethodSymbol method, string message)> Errors;

        private static readonly ConditionalWeakTable<Compilation, ContractStubs> _cache = new ConditionalWeakTable<Compilation, ContractStubs>();

        public static ContractStubs For(Compilation compilation) => _cache.GetValue(compilation, c => new ContractStubs(c));

        private ContractStubs(Compilation compilation)
        {
            var errors = new List<(IMethodSymbol, string)>();
            var models = new List<IMethodSymbol>();
            var assemblies = new List<IAssemblySymbol> { compilation.Assembly };
            var spec = compilation.GetTypeByMetadataName(SpecSymbols.Namespace + ".ContractsForAttribute")?.ContainingAssembly;
            if (spec != null && !SymbolEqualityComparer.Default.Equals(spec, compilation.Assembly)) assemblies.Add(spec);
            // the user's first: theirs win (and the CsVerify library's, compiled from source here, come after)
            var types = assemblies.SelectMany(a => AllTypes(a.GlobalNamespace)).OrderBy(t => IsLibrary(t) ? 1 : 0).ToList();
            foreach (var type in types)
            {
                foreach (var m in type.GetMembers().OfType<IMethodSymbol>().Where(SpecSymbols.IsModel))
                {
                    if (!m.IsStatic || m.Parameters.Length < 1 || m.Parameters.Length > 2 || m.ReturnsVoid || m.Parameters.Any(p => p.RefKind != RefKind.None))
                        errors.Add((m, $"[Model] '{m.Name}' must be static, return a value, and take the object (and at most one key)"));
                    else if (m.Parameters[0].Type.IsValueType)
                        errors.Add((m, $"[Model] '{m.Name}': its first parameter, the object, must be of a reference type"));
                    else if (m.Parameters.Length == 2 && SpecSymbols.IsSeqType(m.ReturnType))
                        errors.Add((m, $"[Model] '{m.Name}' with a key cannot return a ghost collection"));
                    else models.Add(m);
                }
                var target = SpecSymbols.ContractsForTarget(type)?.OriginalDefinition;
                if (target == null) continue;
                if (SpecSymbols.HasAttribute(type, "MustDisposeAttribute")) MustDisposeTargets.Add(target);
                if (type.TypeParameters.Length != target.TypeParameters.Length)
                {
                    errors.Add((type.GetMembers().OfType<IMethodSymbol>().FirstOrDefault(), $"stub {type.Name} must have the type parameters of {target.Name} ({target.TypeParameters.Length})"));
                    continue;
                }
                foreach (var m in type.GetMembers().OfType<IMethodSymbol>())
                {
                    if (m.MethodKind != MethodKind.Ordinary || m.IsImplicitlyDeclared || SpecSymbols.IsModel(m) || SpecSymbols.IsGhostFunction(m) ||
                        SpecSymbols.IsLemma(m) || SpecSymbols.IsPredicate(m)) continue;
                    var member = Match(target, m);
                    if (member == null)
                    {
                        errors.Add((m, $"stub '{m.Name}' matches no member of {target.ToDisplayString()} (instance members take '@this' first, constructors are '@new', accessors are get_P/set_P)"));
                        continue;
                    }
                    // a [Comprehensions] class defines its members (as queries), and is not their contract
                    var into = SpecSymbols.HasAttribute(type, "ComprehensionsAttribute") ? _queryOf : _stubOf;
                    if (into.ContainsKey(member)) continue; // (a source stub came first)
                    into[member] = m;
                    if (into == _stubOf) _stubs.Add(m);
                }
            }
            Models = models.OrderBy(m => m.ToDisplayString()).ToList();
            Errors = errors;
        }

        /// <summary>From the CsVerify library (as a reference, or as its sources compiled in by the verifier)?</summary>
        private static bool IsLibrary(INamedTypeSymbol t) =>
            t.Locations.All(l => !l.IsInSource || l.SourceTree?.FilePath?.StartsWith("<CsVerify.Spec>") == true);

        private static IEnumerable<INamedTypeSymbol> AllTypes(INamespaceSymbol ns)
        {
            foreach (var t in ns.GetTypeMembers()) foreach (var x in WithNested(t)) yield return x;
            foreach (var sub in ns.GetNamespaceMembers()) foreach (var x in AllTypes(sub)) yield return x;
        }

        private static IEnumerable<INamedTypeSymbol> WithNested(INamedTypeSymbol t)
        {
            yield return t;
            foreach (var n in t.GetTypeMembers()) foreach (var x in WithNested(n)) yield return x;
        }

        /// <summary>The stub method giving <paramref name="member"/> its contract, if any.</summary>
        public IMethodSymbol StubOf(IMethodSymbol member)
        {
            if (member == null) return null;
            member = (member.ReducedFrom ?? member).OriginalDefinition;
            return _stubOf.TryGetValue(member, out var s) ? s : null;
        }

        /// <summary>The [Comprehensions] method defining <paramref name="member"/> (a LINQ method), if any.</summary>
        public IMethodSymbol QueryOf(IMethodSymbol member)
        {
            if (member == null) return null;
            member = (member.ReducedFrom ?? member).OriginalDefinition;
            return _queryOf.TryGetValue(member, out var s) ? s : null;
        }

        /// <summary>Every member a [Comprehensions] method defines, and its definition (for the conformance tests).</summary>
        public IEnumerable<(IMethodSymbol member, IMethodSymbol query)> QueryPairs => _queryOf.Select(kv => (kv.Key, kv.Value));

        /// <summary>Every member with a stub, and its stub (for the conformance tests, which run them).</summary>
        public IEnumerable<(IMethodSymbol member, IMethodSymbol stub)> Pairs => _stubOf.Select(kv => (kv.Key, kv.Value));

        /// <summary>Is this method a stub (one that specifies an external member)?</summary>
        public bool IsStub(IMethodSymbol m) => m != null && _stubs.Contains(m.OriginalDefinition);

        /// <summary>A stub for an instance member: its first parameter, <c>@this</c>, is the receiver.</summary>
        public static bool TakesReceiver(IMethodSymbol stub) => stub.Name != "new" && stub.Parameters.Length > 0 && stub.Parameters[0].Name == "this";

        /// <summary>Is <paramref name="m"/> a [Pure] external member (through its stub)?</summary>
        public bool IsPureMember(IMethodSymbol m) => StubOf(m) is IMethodSymbol s && SpecSymbols.IsPure(s);

        private static IMethodSymbol Match(INamedTypeSymbol target, IMethodSymbol stub)
        {
            bool ctor = stub.Name == "new";
            bool instance = TakesReceiver(stub);
            var parameters = instance ? stub.Parameters.Skip(1).ToList() : stub.Parameters.ToList();
            if (instance && !Same(stub.Parameters[0].Type, target, null)) return null;
            IEnumerable<IMethodSymbol> candidates;
            if (ctor) candidates = target.InstanceConstructors;
            else
            {
                candidates = target.GetMembers(stub.Name).OfType<IMethodSymbol>();
                // a getter by its property's name
                if (instance && parameters.Count == 0)
                    candidates = candidates.Concat(target.GetMembers(stub.Name).OfType<IPropertySymbol>().Where(p => !p.IsIndexer && p.GetMethod != null).Select(p => p.GetMethod));
                else if (!instance && parameters.Count == 0)
                    candidates = candidates.Concat(target.GetMembers(stub.Name).OfType<IPropertySymbol>().Where(p => p.IsStatic && p.GetMethod != null).Select(p => p.GetMethod));
            }
            foreach (var c in candidates)
            {
                if (!ctor && c.IsStatic == instance) continue;
                if (c.Parameters.Length != parameters.Count || c.TypeParameters.Length != stub.TypeParameters.Length) continue;
                bool ok = true;
                for (int i = 0; i < parameters.Count && ok; i++)
                    ok = parameters[i].RefKind == c.Parameters[i].RefKind && Same(parameters[i].Type, c.Parameters[i].Type, c);
                if (!ok) continue;
                if (ctor ? !Same(stub.ReturnType, target, null) : !(stub.ReturnsVoid == c.ReturnsVoid && (c.ReturnsVoid || Same(stub.ReturnType, c.ReturnType, c)))) continue;
                return c.OriginalDefinition;
            }
            return null;
        }

        /// <summary>
        /// A stub's type <paramref name="s"/> and a member's <paramref name="t"/> are the same, with the stub's type
        /// parameters standing for the external type's (and its method's for the member's), by position.
        /// </summary>
        private static bool Same(ITypeSymbol s, ITypeSymbol t, IMethodSymbol member)
        {
            switch (s)
            {
                case ITypeParameterSymbol sp:
                    return t is ITypeParameterSymbol tp && tp.TypeParameterKind == sp.TypeParameterKind && tp.Ordinal == sp.Ordinal;
                case IArrayTypeSymbol sa:
                    return t is IArrayTypeSymbol ta && ta.Rank == sa.Rank && Same(sa.ElementType, ta.ElementType, member);
                case INamedTypeSymbol sn:
                    if (!(t is INamedTypeSymbol tn) || !SymbolEqualityComparer.Default.Equals(sn.OriginalDefinition, tn.OriginalDefinition)) return false;
                    var sargs = sn.TypeArguments;
                    // the target itself, as typeof(List<>) gives it: its own type parameters
                    var targs = tn.IsUnboundGenericType ? tn.OriginalDefinition.TypeArguments : tn.TypeArguments;
                    for (int i = 0; i < sargs.Length; i++)
                        if (!Same(sargs[i], targs[i], member)) return false;
                    return true;
                default:
                    return SymbolEqualityComparer.Default.Equals(s, t);
            }
        }
    }
}
