using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// A collection's members called, or its indexer written, through IList&lt;T&gt; or ICollection&lt;T&gt;:
    /// by what the object is. An array's: a fixed size (Add, Insert, Remove, RemoveAt and Clear throw
    /// NotSupportedException), its indexer its element; a List's: the List's stub; any other collection's: a library
    /// call, which says nothing of what it then holds. (Reads through the interfaces are Lowering's Ifc.)
    /// </summary>
    internal sealed partial class Lowering
    {
        private static bool IsListInterface(ITypeSymbol t) =>
            t is INamedTypeSymbol { Arity: 1 } n && n.ContainingNamespace?.ToDisplayString() == "System.Collections.Generic" && n.Name is "IList" or "ICollection";

        /// <summary>The blocks of a two-way choice: where cond holds, where it doesn't, and where they join.</summary>
        private sealed class IfBlocks
        {
            public KBlock Yes, No, Join;
        }

        /// <summary>
        /// Two ways from here, joined after: the current block ends in a choice, and what's lowered next is the way where
        /// cond holds (until Else, then the other way, until EndIf).
        /// </summary>
        private IfBlocks If(KExpr cond)
        {
            var from = _block;
            var name = $"{from.Label}$if{_temps++}";
            var b = new IfBlocks
            {
                Yes = KBlock.Of(name + "t", from.Ordinal),
                No = KBlock.Of(name + "f", from.Ordinal),
                Join = KBlock.Of(name + "j", from.Ordinal),
            };
            b.Yes.AddStmt(KAssume.Of(cond));
            b.No.AddStmt(KAssume.Of(Not(cond)));
            from.Jump = new KGoto(b.Yes.Label, b.No.Label);
            _p.AddBlock(b.Yes);
            _block = b.Yes;
            return b;
        }

        /// <summary>The way where the condition holds ends (on to the join); the other way's is lowered next.</summary>
        private void Else(IfBlocks b)
        {
            _block.Jump = new KGoto(b.Join.Label);
            _p.AddBlock(b.No);
            _block = b.No;
        }

        /// <summary>The other way ends (on to the join), and lowering goes on after the choice.</summary>
        private void EndIf(IfBlocks b)
        {
            _block.Jump = new KGoto(b.Join.Label);
            _p.AddBlock(b.Join);
            _block = b.Join;
        }

        /// <summary>An array's member that would change its size: NotSupportedException (where exceptions are seen, to their handlers), and nothing after.</summary>
        private void FixedSize()
        {
            if (_cfgBlock != null && ThrowTarget(_cfgBlock.EnclosingRegion) is string target)
            {
                Emit(new KFork
                {
                    Overflow = KLit.False,
                    Target = target,
                    Exception = null,
                });
            }
            Emit(KAssume.Of(KLit.False));
        }

        /// <summary>A call through IList or ICollection of a member that changes the collection: its value, handled; else (false, null).</summary>
        private (bool, KExpr) IfcCall(IInvocationOperation call)
        {
            var m = call.TargetMethod;
            if (call.Instance == null || !IsListInterface(m.ContainingType) || !(m.Name is "Add" or "Insert" or "Remove" or "RemoveAt" or "Clear"))
            {
                return (false, null);
            }
            var ifc = (INamedTypeSymbol)m.ContainingType;
            var element = ifc.TypeArguments[0];
            if (!InSubset(element))
            {
                return (false, null);
            }
            // (the program's own implementations: a call through the interface runs its code)
            if (new[] { "IList", "ICollection" }.Any(n => KernelTypes.Compilation.GetTypeByMetadataName($"System.Collections.Generic.{n}`1") is INamedTypeSymbol d && ImplementedHere(d)))
            {
                return (false, null);
            }
            var list = KernelTypes.Compilation.GetTypeByMetadataName("System.Collections.Generic.List`1").Construct(element);
            var target = list.GetMembers(m.Name).OfType<IMethodSymbol>().FirstOrDefault(x => x.Parameters.Length == m.Parameters.Length &&
                x.Parameters.Zip(m.Parameters, (a, b) => SymbolEqualityComparer.Default.Equals(a.Type, b.Type)).All(s => s));
            if (target == null)
            {
                return (false, null);
            }
            var receiver = Expr(call.Instance);
            Emit(KCheck.Of(NotNull(receiver), "CSV1013", call.Instance.Syntax, $"'{call.Instance.Syntax}' might be null in '{call.Syntax}'"));
            KExpr value = null;
            string result = m.ReturnsVoid ? null : Declare("t$" + _temps++, m.ReturnType);
            // (an array: its size is fixed)
            var isArray = If(new KOp("$arr", receiver));
            FixedSize();
            Else(isArray);
            // (a List: its own member)
            var isList = If(new KOp("$coll", receiver));
            foreach (var md in ModelsOf(list))
            {
                _p.Models[md.Name] = md;
            }
            var listValue = Invoke(target, call.Instance, call.Arguments, call.Syntax, null);
            if (result != null)
            {
                Emit(KAssign.Of(result, listValue));
            }
            Else(isList);
            // (any other collection: the library's)
            var (handled, otherValue) = LibraryCall(call);
            if (!handled)
            {
                throw new NotTranslated($"{m.Name} through {ifc.Name} of a collection the kernel doesn't model");
            }
            if (result != null)
            {
                Emit(KAssign.Of(result, otherValue));
            }
            EndIf(isList);
            EndIf(isArray);
            if (result != null)
            {
                value = new KVar(result);
            }
            return (true, value);
        }

        /// <summary>l[i] = v through IList: an array's element, a List's setter, or (any other collection) the library's.</summary>
        private bool IfcIndexerWrite(IOperation target, KExpr value)
        {
            if (!(target is IPropertyReferenceOperation { Property.IsIndexer: true } pr) || pr.Instance == null || pr.Arguments.Length != 1 ||
                !(pr.Property.ContainingType is INamedTypeSymbol { Name: "IList", Arity: 1 } ifc) || ifc.ContainingNamespace?.ToDisplayString() != "System.Collections.Generic")
            {
                return false;
            }
            var element = ifc.TypeArguments[0];
            if (!InSubset(element))
            {
                return false;
            }
            if (KernelTypes.Compilation.GetTypeByMetadataName("System.Collections.Generic.IList`1") is INamedTypeSymbol d && ImplementedHere(d))
            {
                return false;
            }
            var list = KernelTypes.Compilation.GetTypeByMetadataName("System.Collections.Generic.List`1").Construct(element);
            var setter = list.GetMembers().OfType<IPropertySymbol>().FirstOrDefault(p => p.IsIndexer)?.SetMethod;
            if (setter == null)
            {
                return false;
            }
            var receiver = Expr(pr.Instance);
            var index = Expr(pr.Arguments[0].Value);
            var v = Declare("t$" + _temps++, element);
            Emit(KAssign.Of(v, value));
            Emit(KCheck.Of(NotNull(receiver), "CSV1013", pr.Instance.Syntax, $"'{pr.Instance.Syntax}' might be null in '{pr.Syntax}'"));
            var array = KernelTypes.Compilation.CreateArrayTypeSymbol(element);
            // (an array: its element)
            var isArray = If(new KOp("$arr", receiver));
            HeldCell(receiver, pr.Syntax, write: true);
            Emit(new KStore
            {
                Array = receiver,
                Index = index,
                Value = new KVar(v),
                ArrayType = array,
                At = pr.Syntax,
                ArrayAt = pr.Instance.Syntax,
            });
            Else(isArray);
            // (a List: its setter)
            var isList = If(new KOp("$coll", receiver));
            foreach (var md in ModelsOf(list))
            {
                _p.Models[md.Name] = md;
            }
            Invoke(setter, pr.Instance, pr.Arguments, pr.Syntax, new KVar(v));
            Else(isList);
            // (another collection's setter: code the kernel doesn't know, which may change anything)
            _p.HavocsAll = true;
            _p.CallsDelegates = true;
            Emit(new KHavocAll());
            EndIf(isList);
            EndIf(isArray);
            return true;
        }
    }
}
