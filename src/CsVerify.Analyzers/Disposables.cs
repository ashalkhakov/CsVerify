using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using Microsoft.CodeAnalysis;

namespace CsVerify.Analyzers
{
    /// <summary>
    /// Which objects must be disposed (see <see cref="DisposalAnalyzer"/>): those of a [MustDispose] class, of a
    /// library type a [MustDispose] stub marks, or of a class that owns a field of such a type (it holds the resource
    /// in turn). And which parameters take what they are handed ([TakesOwnership], on the method or on its stub).
    /// </summary>
    public sealed class Disposables
    {
        private static readonly ConditionalWeakTable<Compilation, Disposables> _cache = new ConditionalWeakTable<Compilation, Disposables>();
        public static Disposables For(Compilation compilation) => _cache.GetValue(compilation, c => new Disposables(c));

        private readonly ContractStubs _stubs;
        private readonly Dictionary<ITypeSymbol, bool> _must = new Dictionary<ITypeSymbol, bool>(SymbolEqualityComparer.Default);

        private Disposables(Compilation compilation) { _stubs = ContractStubs.For(compilation); }

        // the types being decided on this thread (a class owning a field of its own type): no to them meanwhile
        [System.ThreadStatic] private static HashSet<ITypeSymbol> _deciding;

        public bool MustDispose(ITypeSymbol type)
        {
            if (type == null || type.TypeKind != TypeKind.Class) return false;
            var key = type.OriginalDefinition;
            lock (_must) if (_must.TryGetValue(key, out var known)) return known;
            _deciding ??= new HashSet<ITypeSymbol>(SymbolEqualityComparer.Default);
            if (!_deciding.Add(key)) return false;
            bool result = false;
            try
            {
                for (var t = type as INamedTypeSymbol; t != null && !result; t = t.BaseType)
                    result = SpecSymbols.HasAttribute(t.OriginalDefinition, "MustDisposeAttribute") || _stubs.MustDisposeTargets.Contains(t.OriginalDefinition) ||
                             t.DeclaringSyntaxReferences.Length > 0 && OwnedFields(t).Any();
            }
            finally { _deciding.Remove(key); }
            // (only a decision made outside any other is final: inside one, a type being decided counted as no)
            if (_deciding.Count == 0) lock (_must) _must[key] = result;
            return result;
        }

        /// <summary>The fields (and auto-properties) a class declares that hold disposables it owns.</summary>
        public IEnumerable<ISymbol> OwnedFields(INamedTypeSymbol type) =>
            type.GetMembers().Where(m => !m.IsStatic && !m.IsImplicitlyDeclared && !SpecSymbols.HasAttribute(m, "NotOwnedAttribute") &&
                                         (m is IFieldSymbol f && f.AssociatedSymbol == null && MustDispose(f.Type) ||
                                          m is IPropertySymbol p && IsAuto(p) && MustDispose(p.Type)));

        private static bool IsAuto(IPropertySymbol p) =>
            p.ContainingType.GetMembers().OfType<IFieldSymbol>().Any(f => SymbolEqualityComparer.Default.Equals(f.AssociatedSymbol, p));

        /// <summary>Does this parameter take the disposable it is handed (so the caller is done with it)?</summary>
        public bool TakesOwnership(IParameterSymbol p)
        {
            if (p == null) return false;
            if (SpecSymbols.HasAttribute(p.OriginalDefinition, "TakesOwnershipAttribute")) return true;
            var m = p.ContainingSymbol as IMethodSymbol;
            if (m == null || !(_stubs.StubOf(m.OriginalDefinition) is IMethodSymbol stub)) return false;
            int i = p.Ordinal + (ContractStubs.TakesReceiver(stub) ? 1 : 0);
            return i < stub.Parameters.Length && SpecSymbols.HasAttribute(stub.Parameters[i], "TakesOwnershipAttribute");
        }
    }
}
