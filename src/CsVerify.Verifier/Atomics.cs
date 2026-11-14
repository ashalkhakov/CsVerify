using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Fields shared without a lock (<c>[Atomic]</c>): read and written one atomic step at a time by any thread. What a
    /// thread knows of one is what it last read or wrote, and that every change since is a step of its relation
    /// (<c>Step</c>), which is transitive. So each read sees a value one or more steps on, and each write is proved a step
    /// from whatever it replaces: a fact a thread derives from it stays true whatever the others do, as rely-guarantee
    /// reasoning has it, with the step as both the rely and the guarantee.
    /// </summary>
    internal sealed class Atomics
    {
        private readonly IReadOnlyList<INamedTypeSymbol> _types;
        private readonly HashSet<SyntaxNode> _claimed = new HashSet<SyntaxNode>();
        private List<(SyntaxNode at, string message)> _misdeclared;
        private List<IFieldSymbol> _all;

        public Atomics(IReadOnlyList<INamedTypeSymbol> types)
        {
            _types = types;
        }

        public static bool IsAtomic(ISymbol field) =>
            field is IFieldSymbol f && SpecSymbols.HasAttribute(f.OriginalDefinition, "AtomicAttribute");

        private static string StepName(IFieldSymbol f) =>
            f.OriginalDefinition.GetAttributes().FirstOrDefault(a => a.AttributeClass?.Name == "AtomicAttribute")?
                .NamedArguments.FirstOrDefault(kv => kv.Key == "Step").Value.Value as string;

        /// <summary>The field's step relation, if it has one that is well formed; null for any change.</summary>
        public static IMethodSymbol StepOf(ISymbol field) =>
            field is IFieldSymbol f && StepName(f) is string name
                ? f.ContainingType.GetMembers(name).OfType<IMethodSymbol>().FirstOrDefault(m => WellFormedStep(m, f) == null)
                : null;

        public IReadOnlyList<IFieldSymbol> All =>
            _all ??= _types.SelectMany(t => t.GetMembers().OfType<IFieldSymbol>()).Where(IsAtomic).ToList();

        /// <summary>The atomic fields with a step: those whose maps, wherever they're forgotten, are known to have moved by steps.</summary>
        public IEnumerable<IFieldSymbol> Stepped => All.Where(f => StepOf(f) != null);

        /// <summary>Is this method the step of some atomic field? Then it is proved transitive.</summary>
        public IEnumerable<IFieldSymbol> SteppedBy(IMethodSymbol m) =>
            All.Where(f => StepName(f) == m.Name && SymbolEqualityComparer.Default.Equals(f.ContainingType, m.ContainingType));

        public bool Claim(SyntaxNode at) => _claimed.Add(at);

        /// <summary>A type whose values are read and written in one step, and compared by ==: an integer, a bool, a char, an enum, a reference.</summary>
        public static bool AtomicType(ITypeSymbol t)
        {
            if (t == null)
            {
                return false;
            }
            if (t.TypeKind == TypeKind.Enum)
            {
                return true;
            }
            switch (t.SpecialType)
            {
                case SpecialType.System_Boolean: case SpecialType.System_Char:
                case SpecialType.System_SByte: case SpecialType.System_Byte:
                case SpecialType.System_Int16: case SpecialType.System_UInt16:
                case SpecialType.System_Int32: case SpecialType.System_UInt32:
                case SpecialType.System_Int64: case SpecialType.System_UInt64:
                    return true;
            }
            return t.IsReferenceType;
        }

        private static string WellFormedStep(IMethodSymbol m, IFieldSymbol f)
        {
            if (!m.IsStatic)
            {
                return "must be static";
            }
            if (!SpecSymbols.HasAttribute(m, "PureAttribute"))
            {
                return "must be [Pure]";
            }
            if (m.ReturnType.SpecialType != SpecialType.System_Boolean)
            {
                return "must return bool";
            }
            if (m.Parameters.Length != 2 || m.Parameters.Any(p => p.RefKind != RefKind.None || !SymbolEqualityComparer.Default.Equals(p.Type, f.Type)))
            {
                return $"must take two {f.Type.ToDisplayString()} values, the old and the new";
            }
            return null;
        }

        /// <summary>
        /// Atomic fields that can't be: of a type with no one-step reads and writes, readonly, guarded by a lock, in an
        /// [Owned] class, with a step that isn't a static [Pure] bool method of two values of its type, or that reads state.
        /// </summary>
        public IReadOnlyList<(SyntaxNode at, string message)> Misdeclared(FieldEffects fields, LockGuards locks)
        {
            if (_misdeclared != null)
            {
                return _misdeclared;
            }
            _misdeclared = new List<(SyntaxNode, string)>();
            foreach (var f in All)
            {
                if (!(f.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is VariableDeclaratorSyntax at))
                {
                    continue;
                }
                if (!AtomicType(f.Type))
                {
                    AddMisdeclared($"is a {f.Type.ToDisplayString()}: an atomic field is an integer, a bool, a char, an enum or a reference, read and written in one step", at, f);
                }
                if (f.IsReadOnly || f.IsConst)
                {
                    AddMisdeclared("never changes: it needs no [Atomic]", at, f);
                }
                if (SpecSymbols.HasAttribute(f, "GuardedByAttribute"))
                {
                    AddMisdeclared("is also [GuardedBy] a lock: it's one or the other", at, f);
                }
                if (!f.IsStatic && SpecSymbols.IsOwned(f.ContainingType))
                {
                    AddMisdeclared($"is in [Owned] '{f.ContainingType.Name}', whose fields are held by one owner at a time", at, f);
                }
                if (SpecSymbols.HasAttribute(f, "LockLevelAttribute"))
                {
                    AddMisdeclared("is a lock: a lock field never changes", at, f);
                }
                if (locks.IsFlag(f))
                {
                    AddMisdeclared("guards state, so it's a try-lock, taken and given back in its form: it's one or the other", at, f);
                }
                if (f.ContainingType.IsValueType && !f.IsStatic)
                {
                    AddMisdeclared($"is in struct '{f.ContainingType.Name}', which is copied, not shared", at, f);
                }
                if (StepName(f) is string name)
                {
                    var m = f.ContainingType.GetMembers(name).OfType<IMethodSymbol>().ToList();
                    if (m.Count != 1)
                    {
                        AddMisdeclared($"names a step '{name}' that isn't one method of '{f.ContainingType.Name}'", at, f);
                    }
                    else if (WellFormedStep(m[0], f) is string why)
                    {
                        AddMisdeclared($"names a step '{name}' that {why}", at, f);
                    }
                    else if (fields.ReadsOf(m[0]).Count > 0 || fields.ReadsArrays(m[0]))
                    {
                        AddMisdeclared($"names a step '{name}' that reads state: it may only look at the old and new values", at, f);
                    }
                }
            }
            // what changes at any moment can't be in a function, a predicate or an invariant, which are of one state
            foreach (var m in _types.SelectMany(t => t.GetMembers().OfType<IMethodSymbol>()))
            {
                bool ofOneState = SpecSymbols.IsPure(m) || SpecSymbols.IsPredicate(m) || SpecSymbols.IsInvariant(m) || SpecSymbols.HasAttribute(m, "LockInvariantAttribute");
                if (!ofOneState || m.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is not SyntaxNode decl)
                {
                    continue;
                }
                if (fields.ReadsOf(m).FirstOrDefault(IsAtomic) is ISymbol read)
                {
                    _misdeclared.Add((decl, $"'{m.Name}' reads [Atomic] '{read.Name}', which other threads change at any moment: a function, predicate or invariant is of one state. Read it in code, or say what's known of it in a specification"));
                }
            }
            return _misdeclared;
        }

        private void AddMisdeclared(string why, VariableDeclaratorSyntax at, IFieldSymbol f) => _misdeclared.Add((at, $"[Atomic] '{f.Name}' {why}"));
    }
}
