using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Heap fields (see <see cref="FieldEffects"/>): each is an SMT array from object to value. A frame holds the
    /// maps changed on its path; an unchanged one is the map as of the frame's epoch (the method's entry state,
    /// or the state after a call that may have written anything), shared by every path and by <c>Spec.Old</c>.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private readonly Dictionary<string, Term> _fieldStates = new Dictionary<string, Term>();
        private int _fieldEpochs;

        private Term FieldMap(Frame f, ISymbol field)
        {
            field = FieldEffects.Key(field);
            if (f.Fields.TryGetValue(field, out var map)) return map;
            var key = field.ToDisplayString() + "#" + f.FieldEpoch;
            if (!_fieldStates.TryGetValue(key, out map))
                _fieldStates[key] = map = _z3.Fresh(field.Name + "$map", Sort.Row);
            return map;
        }

        private Term ReadField(ISymbol field, IOperation instance, ITypeSymbol type, SyntaxNode at, Frame f, SpecEnv spec)
        {
            var o = Eval(instance, f, spec);
            Deref(instance, o, at);
            return T.Coerce(T.Select(FieldMap(f, field), o, Sort.Int), SortOf(type));
        }

        private void WriteField(ISymbol field, IOperation instance, Term v, SyntaxNode at, Frame f, SpecEnv spec)
        {
            var o = Eval(instance, f, spec);
            Deref(instance, o, at);
            f.Fields[FieldEffects.Key(field)] = T.Store(FieldMap(f, field), o, T.Coerce(v, Sort.Int));
        }

        /// <summary>After a call: the heap fields it may write have unknown values (an inferred frame condition).</summary>
        private void HavocFields(Frame f, IMethodSymbol callee)
        {
            var (fields, all) = _engine.Fields.WritesOf(callee);
            if (all) HavocAllFields(f);
            foreach (var field in fields) f.Fields[field] = _z3.Fresh(field.Name + "$map", Sort.Row);
        }

        private void HavocAllFields(Frame f)
        {
            f.Fields.Clear();
            f.FieldEpoch = ++_fieldEpochs;
        }

        private static bool HasInitializer(ISymbol field) =>
            field.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).Any(s =>
                s is VariableDeclaratorSyntax v && v.Initializer != null || s is PropertyDeclarationSyntax p && p.Initializer != null);

        private static bool DeclaredIn(ISymbol field, ITypeSymbol type) =>
            SymbolEqualityComparer.Default.Equals(field.ContainingType.OriginalDefinition, type.OriginalDefinition);

        /// <summary>A constructor chaining to another source constructor (<c>this(...)</c>, or <c>base(...)</c> of a source class).</summary>
        private static ConstructorInitializerSyntax ChainedInitializer(IMethodSymbol ctor, SemanticModel model)
        {
            foreach (var cd in ctor.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).OfType<ConstructorDeclarationSyntax>())
                if (cd.Initializer != null && model.Compilation.GetSemanticModel(cd.SyntaxTree).GetSymbolInfo(cd.Initializer).Symbol is IMethodSymbol target &&
                    target.DeclaringSyntaxReferences.Length > 0)
                    return cd.Initializer;
            return null;
        }

        /// <summary>
        /// Verifying a constructor: the new object's own fields start at their defaults, then the field
        /// initializers run, then the body.
        /// </summary>
        private void EnterConstructor(Frame f)
        {
            var type = _method.ContainingType;
            if (ChainedInitializer(_method, _model) is ConstructorInitializerSyntax chained)
            {
                NotModeled(chained, "constructor chaining (this(...), or base(...) of a source class) is not supported yet");
                return;
            }
            var own = FieldEffects.FieldsOf(type).Where(s => DeclaredIn(s, type)).ToList();
            foreach (var field in own)
                _z3.Assume(T.Eq(T.Select(FieldMap(f, field), f.This, Sort.Int), T.Int(0)));
            bool wasCode = _codeMode;
            _codeMode = true;
            try
            {
                foreach (var field in own)
                {
                    var init = field.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).Select(s =>
                        (SyntaxNode)(s as VariableDeclaratorSyntax)?.Initializer ?? (s as PropertyDeclarationSyntax)?.Initializer).FirstOrDefault(i => i != null);
                    if (init == null) continue;
                    if (!(_engine.ModelOf(init.SyntaxTree).GetOperation(init) is ISymbolInitializerOperation op)) { NotModeled(init, "unsupported initializer"); continue; }
                    var v = Eval(op.Value, f);
                    f.Fields[field] = T.Store(FieldMap(f, field), f.This, T.Coerce(v, Sort.Int));
                }
            }
            finally { _codeMode = wasCode; }
        }

        /// <summary>
        /// <c>new C(...)</c> of an ordinary class: a fresh object, distinct from every reference in scope. Its own
        /// fields are what the constructor or an initializer sets (unknown, unless the constructor's postcondition
        /// says) or else their defaults; whatever else the constructor writes is forgotten.
        /// </summary>
        private void SetNewObjectFields(Frame f, Term obj, ITypeSymbol type, IMethodSymbol ctor)
        {
            foreach (var kv in f.Vars)
                if ((kv.Key is ILocalSymbol || kv.Key is IParameterSymbol) && MayBeNullType(TypeOf(kv.Key)) && kv.Value.Sort == Sort.Int)
                    AssumeSide(T.Not(T.Eq(obj, kv.Value)));
            if (f.This != null) AssumeSide(T.Not(T.Eq(obj, f.This)));
            if (ctor != null) HavocFields(f, ctor);
            var set = ctor != null ? _engine.Fields.SelfWritesOf(ctor) : new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            bool chains = ctor != null && ChainedInitializer(ctor, _model) != null;
            foreach (var field in FieldEffects.FieldsOf(type))
            {
                bool unknown = chains || set.Contains(field) || HasInitializer(field) || !DeclaredIn(field, type);
                var value = unknown ? _z3.Fresh(field.Name, Sort.Int) : T.Int(0);
                f.Fields[field] = T.Store(FieldMap(f, field), obj, value);
            }
        }
    }
}
