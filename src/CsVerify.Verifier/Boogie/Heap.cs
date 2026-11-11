using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// Pass 3: memory as Dafny encodes it. A write of an array's element (checked by now) is an update of its element
    /// type's map, and a write of a field one of the field's map; new T[n] is a reference not allocated before, of
    /// length n, then allocated, its elements the default (or the initializer's); new C(...) is an object allocated
    /// so, its fields their defaults, then its constructor called on it. What a procedure writes it modifies (the
    /// program closes it over calls); what it writes only at this object in a constructor, or at objects it
    /// allocates, is unchanged at every other object.
    /// </summary>
    internal static class Heap
    {
        /// <summary>The globals, in the order a modifies clause lists them (the field maps after these, by name).</summary>
        public static string[] Globals => new[] { "$Alloc" }.Concat(ElementTypes.Select(ElementMap)).Append("$root").ToArray();

        /// <summary>Allocates t: not null, not allocated before (so no reference in hand), now allocated.</summary>
        private static void Allocate(List<KStmt> stmts, string var, KExpr extra = null)
        {
            var t = new KVar(var);
            stmts.Add(new KHavoc { Var = var });
            KExpr fresh = new KOp("&&", new KOp("!=", t, new KLit("null")), new KOp("!", new KOp("sel", new KVar("$Alloc"), t)));
            stmts.Add(new KAssume { Cond = extra == null ? fresh : new KOp("&&", fresh, extra) });
            stmts.Add(new KMapUpdate { Map = "$Alloc", Ref = t, Value = new KLit("true") });
        }

        public static void Run(KProcedure p)
        {
            LoopFrames(p);
            foreach (var b in p.Blocks)
            {
                var stmts = new List<KStmt>();
                foreach (var s in b.Stmts)
                    switch (s)
                    {
                        case KFieldStore fs:
                        {
                            var map = FieldMap(fs.Field);
                            p.Modifies.Add(map);
                            // (an [Owned] object's field is written only with its view: framed by the views a call gets)
                            if (!(p.IsCtor && fs.OnThis) && !IsOwnedField(fs.Field)) p.AnyWrites.Add(map);
                            stmts.Add(new KMapUpdate { Map = map, Ref = fs.Instance, Value = fs.Value });
                            break;
                        }
                        case KNewObj n:
                        {
                            var t = new KVar(n.Var);
                            p.Modifies.Add("$Alloc");
                            p.AnyWrites.Add("$Alloc");
                            Allocate(stmts, n.Var);
                            foreach (var field in InstanceFields(n.Type))
                            {
                                var map = FieldMap(field);
                                p.Modifies.Add(map);
                                // (a generic class's field of T: the default of a T the class doesn't know, a box nothing is known of)
                                if (!IsTypeParameter(FieldType(field))) stmts.Add(new KMapUpdate { Map = map, Ref = t, Value = Default(FieldType(field)) });
                            }
                            if (n.Ctor != null)
                                stmts.Add(new KCall { Callee = n.Ctor, Receiver = t, ReceiverIsThis = false, Args = n.Args, At = n.At, Check = n.Check });
                            else
                                // an implicit constructor runs the initializers: what they make isn't known here (a non-nullable field's is set)
                                foreach (var field in InstanceFields(n.Type).Where(f => HasInitializer(f) || IsNullable(FieldType(f)) && NotNullable(FieldType(f))))
                                {
                                    var u = "u$" + FieldMap(field);
                                    if (!p.Locals.Any(l => l.Name == u)) p.Locals.Add(new KLocal { Name = u, Type = FieldType(field) });
                                    stmts.Add(new KHavoc { Var = u });
                                    stmts.Add(new KMapUpdate { Map = FieldMap(field), Ref = t, Value = new KVar(u) });
                                }
                            break;
                        }
                        case KRow row when row.Ref == null:
                            // (the whole map: a library call's arrays, any of them)
                            p.Modifies.Add(row.Map);
                            p.AnyWrites.Add(row.Map);
                            stmts.Add(new KAssign { Var = row.Map, Value = row.Value });
                            break;
                        case KRow row:
                            p.Modifies.Add(row.Map);
                            p.AnyWrites.Add(row.Map);
                            stmts.Add(new KMapUpdate { Map = row.Map, Ref = row.Ref, Value = row.Value });
                            break;
                        case KFill fill:
                        {
                            p.Modifies.Add(fill.Map);
                            p.AnyWrites.Add(fill.Map);
                            var j = new KVar("j$");
                            stmts.Add(new KMapUpdate { Map = fill.Map, Ref = new KLit("null"), Value = new KOp("lambda", new KLit("j$: int"),
                                new KOp("ite", new KOp("&&", new KOp("<=", fill.Lo, j), new KOp("<", j, fill.Hi)), fill.Value, new KOp("sel", new KVar(fill.Map), new KLit("null"), j))) });
                            break;
                        }
                        case KStore st:
                        {
                            var map = Elements(st.ArrayType);
                            p.Modifies.Add(map);
                            p.AnyWrites.Add(map);
                            stmts.Add(new KMapUpdate { Map = map, Ref = st.Array, Index = st.Index, Value = st.Value });
                            break;
                        }
                        case KNew n:
                        {
                            var map = Elements(n.ArrayType);
                            var t = new KVar(n.Var);
                            p.Modifies.Add("$Alloc");
                            p.Modifies.Add(map);
                            p.AnyWrites.Add("$Alloc");
                            p.AnyWrites.Add(map);
                            // (a negative size throws: the path ends)
                            stmts.Add(new KAssume { Cond = new KOp(">=", n.Size, new KLit("0")) });
                            Allocate(stmts, n.Var, new KOp("==", new KOp("len", t), n.Size));
                            var zero = ElementValue(map) switch { "bool" => "false", "Ref" => "null", _ => "0" };
                            stmts.Add(new KMapUpdate { Map = map, Ref = t, Value = new KLit($"(lambda j: int :: {zero})") });
                            if (n.Elements != null)
                                for (int k = 0; k < n.Elements.Length; k++)
                                    stmts.Add(new KMapUpdate { Map = map, Ref = t, Index = new KLit(k.ToString()), Value = n.Elements[k] });
                            break;
                        }
                        case KLambda lam:
                            // (a new reference: no other delegate's facts are its)
                            p.Modifies.Add("$Alloc");
                            p.AnyWrites.Add("$Alloc");
                            Allocate(stmts, lam.Var);
                            stmts.Add(lam);
                            break;
                        default:
                            stmts.Add(s);
                            break;
                    }
                b.Stmts = stmts;
            }
        }

        /// <summary>
        /// Each loop that writes arrays only through variables it doesn't change (as CsVerify's engine keeps the rest):
        /// a frame at its head, and a snapshot on each way in. A write through anything else keeps nothing.
        /// </summary>
        private static void LoopFrames(KProcedure p)
        {
            foreach (var (head, last) in p.LoopBodies)
            {
                var body = p.Blocks.Where(b => b.Ordinal >= head && b.Ordinal <= last).ToList();
                var assigned = new HashSet<string>(body.SelectMany(b => b.Stmts).Select(s => s switch
                {
                    KAssign a => a.Var, KCall c => c.Result, KInvoke iv => iv.Result, KLambda lam => lam.Var, KNew n => n.Var, KNewObj o => o.Var, KHavoc h => h.Var, _ => null,
                }).Where(x => x != null));
                var frame = new KLoopFrame { Head = head };
                bool keeps = true;
                foreach (var s in body.SelectMany(b => b.Stmts))
                    switch (s)
                    {
                        case KStore st when st.Array is KVar v && !assigned.Contains(v.Name):
                            if (!frame.Writers.Any(w => ((KVar)w).Name == v.Name)) frame.Writers.Add(v);
                            break;
                        case KStore _: keeps = false; break;
                        case KInvoke _: case KHavocAll _: case KAwait _: keeps = false; break; // (a delegate, or unknown code, may write any array)
                        case KCall c: frame.Callees.Add(c.Callee); break;
                        case KNewObj o when o.Ctor != null: frame.Callees.Add(o.Ctor); break;
                    }
                var entry = p.Blocks.FirstOrDefault(b => b.Label == $"b{head}");
                if (!keeps || entry == null) continue;
                entry.Stmts.Insert(0, frame);
                foreach (var b in p.Blocks.Where(b => b.Ordinal < head && b.Jump is KGoto g && g.Targets.Contains($"b{head}")))
                    b.Stmts.Add(new KSnapshot { Frame = frame });
            }
        }

        private static bool HasInitializer(ISymbol field) =>
            field.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).Any(s =>
                s is Microsoft.CodeAnalysis.CSharp.Syntax.VariableDeclaratorSyntax v && v.Initializer != null ||
                s is Microsoft.CodeAnalysis.CSharp.Syntax.PropertyDeclarationSyntax pd && pd.Initializer != null);
    }
}
