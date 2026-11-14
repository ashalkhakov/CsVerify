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

        /// <summary>Two ways from here, each lowered by its own, joined after: the current block ends in a choice.</summary>
        private void Branch(KExpr cond, System.Action then, System.Action otherwise)
        {
            var from = _block;
            var name = $"{from.Label}$if{_temps++}";
            var yes = new KBlock
            {
                Label = name + "t",
                Ordinal = from.Ordinal,
                Stmts = { KAssume.Of(cond) },
            };
            var no = new KBlock
            {
                Label = name + "f",
                Ordinal = from.Ordinal,
                Stmts = { KAssume.Of(Not(cond)) },
            };
            var join = KBlock.Of(name + "j", from.Ordinal);
            from.Jump = new KGoto(yes.Label, no.Label);
            _p.AddBlock(yes);
            _block = yes;
            then();
            _block.Jump = new KGoto(join.Label);
            _p.AddBlock(no);
            _block = no;
            otherwise();
            _block.Jump = new KGoto(join.Label);
            _p.AddBlock(join);
            _block = join;
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
            Branch(new KOp("$arr", receiver), FixedSize, () =>
                Branch(new KOp("$coll", receiver), () =>
                {
                    foreach (var md in ModelsOf(list))
                    {
                        _p.Models[md.Name] = md;
                    }
                    var v = Invoke(target, call.Instance, call.Arguments, call.Syntax, null);
                    if (result != null)
                    {
                        Emit(KAssign.Of(result, v));
                    }
                }, () =>
                {
                    var (handled, v) = LibraryCall(call);
                    if (!handled)
                    {
                        throw new NotTranslated($"{m.Name} through {ifc.Name} of a collection the kernel doesn't model");
                    }
                    if (result != null)
                    {
                        Emit(KAssign.Of(result, v));
                    }
                }));
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
            Branch(new KOp("$arr", receiver), () =>
            {
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
            }, () =>
                Branch(new KOp("$coll", receiver), () =>
                {
                    foreach (var md in ModelsOf(list))
                    {
                        _p.Models[md.Name] = md;
                    }
                    Invoke(setter, pr.Instance, pr.Arguments, pr.Syntax, new KVar(v));
                }, () =>
                {
                    // (another collection's setter: code the kernel doesn't know, which may change anything)
                    _p.HavocsAll = true;
                    _p.CallsDelegates = true;
                    Emit(new KHavocAll());
                }));
            return true;
        }
    }
}
