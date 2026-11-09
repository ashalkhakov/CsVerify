using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// Pass 3: arrays as Dafny encodes them. A write of an element (checked by now) is an update of its element
    /// type's map; new T[n] is a reference not allocated before, of length n, then allocated, its elements the default
    /// (or the initializer's). What a procedure writes it modifies (the program closes it over calls).
    /// </summary>
    internal static class Heap
    {
        /// <summary>The globals, in the order a modifies clause lists them.</summary>
        public static readonly string[] Globals = new[] { "$Alloc" }.Concat(ElementTypes.Select(ElementMap)).ToArray();

        public static void Run(KProcedure p)
        {
            foreach (var b in p.Blocks)
            {
                var stmts = new List<KStmt>();
                foreach (var s in b.Stmts)
                    switch (s)
                    {
                        case KStore st:
                        {
                            var map = Elements(st.ArrayType);
                            p.Modifies.Add(map);
                            stmts.Add(new KMapUpdate { Map = map, Ref = st.Array, Index = st.Index, Value = st.Value });
                            break;
                        }
                        case KNew n:
                        {
                            var map = Elements(n.ArrayType);
                            var t = new KVar(n.Var);
                            p.Modifies.Add("$Alloc");
                            p.Modifies.Add(map);
                            // (a negative size throws: the path ends)
                            stmts.Add(new KAssume { Cond = new KOp(">=", n.Size, new KLit("0")) });
                            stmts.Add(new KHavoc { Var = n.Var });
                            stmts.Add(new KAssume
                            {
                                Cond = new KOp("&&", new KOp("&&", new KOp("!=", t, new KLit("null")), new KOp("!", new KOp("sel", new KVar("$Alloc"), t))),
                                               new KOp("==", new KOp("len", t), n.Size)),
                            });
                            stmts.Add(new KMapUpdate { Map = "$Alloc", Ref = t, Value = new KLit("true") });
                            bool isBool = ((IArrayTypeSymbol)n.ArrayType).ElementType.SpecialType == SpecialType.System_Boolean;
                            stmts.Add(new KMapUpdate { Map = map, Ref = t, Value = new KLit($"(lambda j: int :: {(isBool ? "false" : "0")})") });
                            if (n.Elements != null)
                                for (int k = 0; k < n.Elements.Length; k++)
                                    stmts.Add(new KMapUpdate { Map = map, Ref = t, Index = new KLit(k.ToString()), Value = n.Elements[k] });
                            break;
                        }
                        default:
                            stmts.Add(s);
                            break;
                    }
                b.Stmts = stmts;
            }
        }
    }
}
