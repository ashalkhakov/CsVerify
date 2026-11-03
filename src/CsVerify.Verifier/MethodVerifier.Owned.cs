using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// ATS-style ownership of [Owned] objects. A view <c>Own&lt;C&gt;</c> is linear (the analyzer sees to that), so at
    /// most one piece of code holds an object's view at a time, and only that code may write the object's fields.
    /// A view's value is the object it owns. Consequences the verifier uses:
    /// <list type="bullet">
    /// <item>a write to an owned field needs a live view of the object in hand (CSV1016);</item>
    /// <item>a call changes an owned object only if its view goes in (by <c>ref</c> or by value), comes out, or the
    /// object is the receiver of one of its class's methods: no other object's fields need to be forgotten;</item>
    /// <item>the class's [Invariant] travels with the view: assumed where a view is received, proved where it is
    /// handed over or given back (CSV1015).</item>
    /// </list>
    /// Reads need no view: objects are garbage-collected, and while this code runs nobody else holds a view it lent.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private static bool IsOwnedField(ISymbol field) => FieldEffects.IsHeapField(field) && SpecSymbols.IsOwned(field.ContainingType);

        /// <summary>Inside a (non-[Pure]) instance method of an owned class, <c>this</c> is held like a <c>ref</c> view.</summary>
        private bool ThisIsView => !_method.IsStatic && SpecSymbols.IsOwned(_method.ContainingType) && !_contract.IsPure;

        private static bool IsViewVariable(ISymbol s) =>
            (s is ILocalSymbol || s is IParameterSymbol) && SpecSymbols.IsOwnType(TypeOf(s));

        /// <summary>A view variable comes alive: it owns an object no other live view owns.</summary>
        private void ViewAlive(ISymbol view, Term v, Frame f)
        {
            foreach (var other in f.LiveViews.Where(o => !SymbolEqualityComparer.Default.Equals(o, view)).ToList())
                if (f.Vars.TryGetValue(other, out var ov)) _z3.Assume(T.Not(T.Eq(ov, v)));
            f.LiveViews.Add(view);
        }

        /// <summary>The local or parameter an operand names, if it is one.</summary>
        private static ISymbol VariableOf(IOperation op)
        {
            switch (Unconverted(op))
            {
                case ILocalReferenceOperation l: return l.Local;
                case IParameterReferenceOperation p: return p.Parameter;
                default: return null;
            }
        }

        private static ITypeSymbol OwnedType(ITypeSymbol ownType) => ((INamedTypeSymbol)ownType).TypeArguments[0];

        private void RequireWriteView(Term o, Frame f, SyntaxNode at, ITypeSymbol type)
        {
            if (!_codeMode || _foreignSpec > 0) return;
            var holders = f.LiveViews.Select(v => Read(f, v)).ToList();
            if (ThisIsView || _method.MethodKind == MethodKind.Constructor && SpecSymbols.IsOwned(_method.ContainingType)) holders.Add(f.This);
            Require(T.Or(holders.Select(h => T.Eq(h, o)).ToArray()), "CSV1016", at,
                $"'{at}' changes an [Owned] {type.Name} without holding its view (Own<{type.Name}>)");
        }

        private Term OwnedInvariant(ITypeSymbol type, Term o, Frame f) =>
            T.And(DataTypes.Invariants(type).Select(inv =>
                AsBool(PureApply(_engine.ContractOf(inv), o, System.Array.Empty<Term>(), f.Heap, Sort.Bool, null, f))).ToArray());

        /// <summary>A view received: its object is not null (views are made for new objects) and satisfies its invariant.</summary>
        private void AssumeOwnedInvariant(ITypeSymbol type, Term o, Frame f)
        {
            _z3.Assume(NotNull(o));
            if (DataTypes.Invariants(type).Any()) _z3.Assume(OwnedInvariant(type, o, f));
        }

        private void ProveOwnedInvariant(ITypeSymbol type, Term o, Frame f, SyntaxNode at, string when)
        {
            if (DataTypes.Invariants(type).Any())
                Prove(OwnedInvariant(type, o, f), "CSV1015", at, $"invariant of {type.Name} might not hold {when}");
        }

        /// <summary>At entry: the views received (parameters, and <c>this</c> in the class's methods) are live, their invariants hold.</summary>
        private void EnterOwned(Frame f)
        {
            var received = new List<Term>();
            foreach (var p in _method.Parameters.Where(p => SpecSymbols.IsOwnType(p.Type) && p.RefKind != RefKind.Out))
            {
                if (p.RefKind != RefKind.In) f.LiveViews.Add(p);
                AssumeOwnedInvariant(OwnedType(p.Type), f.Vars[p], f);
                // views are linear: two in hand at once own two different objects
                foreach (var other in received) _z3.Assume(T.Not(T.Eq(other, f.Vars[p])));
                received.Add(f.Vars[p]);
            }
            if (ThisIsView && _method.MethodKind != MethodKind.Constructor) AssumeOwnedInvariant(_method.ContainingType, f.This, f);
        }

        /// <summary>At a return: views given back (<c>ref</c>, <c>out</c>, and <c>this</c>) satisfy their invariants again.</summary>
        private void ExitOwned(Frame f, SyntaxNode at)
        {
            foreach (var p in _method.Parameters.Where(p => SpecSymbols.IsOwnType(p.Type) && (p.RefKind == RefKind.Ref || p.RefKind == RefKind.Out)))
                if (f.Vars.TryGetValue(p, out var v)) ProveOwnedInvariant(OwnedType(p.Type), v, f, at, $"when the view '{p.Name}' is given back");
            if (ThisIsView && _method.MethodKind != MethodKind.Constructor)
                ProveOwnedInvariant(_method.ContainingType, f.This, f, at, $"when '{_method.Name}' returns");
        }

        /// <summary>
        /// Before a call: the views it receives are handed over (their invariants proved; by value, consumed), and
        /// a method of an owned class needs its receiver's view. Returns the objects the call may change.
        /// </summary>
        private List<Term> HandOver(IInvocationOperation inv, Term receiver, Term[] args, Frame f, Contract callee)
        {
            var m = callee.Method;
            var touched = new List<Term>();
            if (receiver != null && SpecSymbols.IsOwned(m.ContainingType) && !callee.IsPure && !m.IsStatic)
            {
                RequireWriteView(receiver, f, inv.Syntax, m.ContainingType);
                ProveOwnedInvariant(m.ContainingType, receiver, f, inv.Syntax, $"when '{m.Name}' is called on it");
                touched.Add(receiver);
            }
            foreach (var a in inv.Arguments)
            {
                var p = a.Parameter;
                if (p == null || !SpecSymbols.IsOwnType(p.Type) || p.RefKind == RefKind.Out || p.RefKind == RefKind.In) continue;
                ProveOwnedInvariant(OwnedType(p.Type), args[p.Ordinal], f, a.Syntax, $"when its view is handed to '{m.Name}'");
                touched.Add(args[p.Ordinal]);
                if (p.RefKind == RefKind.None && VariableOf(a.Value) is ISymbol consumed) f.LiveViews.Remove(consumed);
            }
            return touched;
        }

        /// <summary>After a call: the views that come back are live again with their invariants (and its receiver's).</summary>
        private void TakeBack(IInvocationOperation inv, Term receiver, Frame f, Contract callee)
        {
            var m = callee.Method;
            foreach (var a in inv.Arguments.Where(a => a.Parameter != null && SpecSymbols.IsOwnType(a.Parameter.Type) &&
                                                       (a.Parameter.RefKind == RefKind.Ref || a.Parameter.RefKind == RefKind.Out)))
                AssumeOwnedInvariant(OwnedType(a.Parameter.Type), Eval(a.Value, f), f);
            if (receiver != null && SpecSymbols.IsOwned(m.ContainingType) && !callee.IsPure && !m.IsStatic)
                AssumeOwnedInvariant(m.ContainingType, receiver, f);
        }

        /// <summary><c>Own.New(new C(...), out view)</c> and <c>Own.Drop(view)</c>.</summary>
        private Term OwnCall(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var m = inv.TargetMethod;
            if (m.Name == "Drop")
            {
                var view = inv.Arguments[0].Value;
                Eval(view, f, spec);
                if (VariableOf(view) is ISymbol dropped) f.LiveViews.Remove(dropped);
                return T.True;
            }
            // a view is made once, for a new object: from an existing one it would be a second view
            var arg = Unconverted(inv.Arguments[0].Value);
            if (!(arg is IObjectCreationOperation))
            {
                Report("CSV1016", inv.Syntax, "Own.New takes ownership of a new object only: its argument must be a 'new' expression", isError: true);
                return Unknown(inv.Type);
            }
            var obj = Eval(arg, f, spec);
            ProveOwnedInvariant(arg.Type, obj, f, inv.Syntax, "when its view is made");
            var outArg = inv.Arguments[1].Value;
            Write(outArg, obj, f, spec);
            return obj;
        }
    }
}
