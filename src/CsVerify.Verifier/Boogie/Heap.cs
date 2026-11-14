using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.MOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// Pass 3, level 2 to level 3 (in place): memory as Dafny encodes it. A write of an array's element (checked by now) is an update of its element
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
        private static void Allocate(List<IHeapStmt> stmts, string var, MExpr extra = null)
        {
            var t = new MVar(var);
            stmts.Add(MHavoc.Of(var));
            MExpr fresh = AndAlso(NotNull(t), Not(Sel("$Alloc", t)));
            stmts.Add(MAssume.Of(extra == null ? fresh : AndAlso(fresh, extra)));
            stmts.Add(MMapUpdate.Of("$Alloc", t, MLit.True));
        }

        /// <summary>Level 2 to level 3: each block's statements made level 3's, then the loop frames added.</summary>
        public static HProcedure Run(MProcedure p)
        {
            // (what Checks asserts at entry is level 3's already: its well-definedness, nothing stored or allocated)
            var entry = p.Entry.Select(s => s as IHeapStmt ?? throw new System.InvalidOperationException("a store or an allocation at entry: " + s.GetType().Name)).ToList();
            var blocks = p.Blocks.Select(b => HBlock.Of(b, Statements(p, b))).ToList();
            var h = HProcedure.Of(p, entry, blocks);
            LoopFrames(p, h);
            return h;
        }

        /// <summary>A block's statements at level 3: stores map updates, allocations made, the rest as they are.</summary>
        private static List<IHeapStmt> Statements(MProcedure p, MBlock b)
        {
            {
                var stmts = new List<IHeapStmt>();
                foreach (var s in b.Stmts)
                {
                    switch (s)
                    {
                        case MFieldStore fs:
                        {
                            var map = FieldMap(fs.Field);
                            p.Source.AddModifies(map);
                            // (an [Owned] object's field is written only with its view: framed by the views a call gets)
                            if (!(p.Source.IsCtor && fs.OnThis) && !IsOwnedField(fs.Field))
                            {
                                p.Source.AddAnyWrite(map);
                            }
                            stmts.Add(MMapUpdate.Of(map, fs.Instance, fs.Value));
                            break;
                        }
                        case MNewObj n:
                        {
                            var t = new MVar(n.Var);
                            p.Source.AddModifies("$Alloc");
                            p.Source.AddAnyWrite("$Alloc");
                            Allocate(stmts, n.Var);
                            foreach (var field in InstanceFields(n.Type))
                            {
                                var map = FieldMap(field);
                                p.Source.AddModifies(map);
                                // (a generic class's field of T: the default of a T the class doesn't know, a box nothing is known of)
                                if (!IsTypeParameter(FieldType(field)))
                                {
                                    stmts.Add(MMapUpdate.Of(map, t, MathTypes.Default(FieldType(field))));
                                }
                            }
                            if (n.Ctor != null)
                            {
                                stmts.Add(MCall.OfConstructor(n, t));
                            }
                            else
                            {
                                // an implicit constructor runs the initializers: what they make isn't known here (a non-nullable field's is set)
                                foreach (var field in InstanceFields(n.Type).Where(f => HasInitializer(f) || IsNullable(FieldType(f)) && NotNullable(FieldType(f))))
                                {
                                    var u = "u$" + FieldMap(field);
                                    if (!p.Source.Locals.Any(l => l.Name == u))
                                    {
                                        p.Source.AddLocal(new KLocal
                                        {
                                            Name = u,
                                            Type = FieldType(field),
                                        });
                                    }
                                    stmts.Add(MHavoc.Of(u));
                                    stmts.Add(MMapUpdate.Of(FieldMap(field), t, new MVar(u)));
                                }
                            }
                            break;
                        }
                        case MRow row when row.Ref == null:
                            // (the whole map: a library call's arrays, any of them)
                            p.Source.AddModifies(row.Map);
                            p.Source.AddAnyWrite(row.Map);
                            stmts.Add(MAssign.Of(row.Map, row.Value));
                            break;
                        case MRow row:
                            p.Source.AddModifies(row.Map);
                            p.Source.AddAnyWrite(row.Map);
                            stmts.Add(MMapUpdate.Of(row.Map, row.Ref, row.Value));
                            break;
                        case MFill fill:
                        {
                            p.Source.AddModifies(fill.Map);
                            p.Source.AddAnyWrite(fill.Map);
                            var j = new MVar("j$");
                            stmts.Add(MMapUpdate.Of(
                                fill.Map,
                                MLit.Null,
                                MapLambda("j$: int",
                        Ite(AndAlso(Le(fill.Lo, j), Lt(j, fill.Hi)), fill.Value, Sel(fill.Map, MLit.Null, j)))));
                            break;
                        }
                        case MStore st:
                        {
                            var map = Elements(st.ArrayType);
                            p.Source.AddModifies(map);
                            p.Source.AddAnyWrite(map);
                            stmts.Add(MMapUpdate.Of(map, st.Array, index: st.Index, value: st.Value));
                            break;
                        }
                        case MNew n:
                        {
                            var map = Elements(n.ArrayType);
                            var t = new MVar(n.Var);
                            p.Source.AddModifies("$Alloc");
                            p.Source.AddModifies(map);
                            p.Source.AddAnyWrite("$Alloc");
                            p.Source.AddAnyWrite(map);
                            // (a negative size throws: the path ends)
                            stmts.Add(MAssume.Of(Ge(n.Size, MLit.Zero)));
                            Allocate(stmts, n.Var, Eq(Length(t), n.Size));
                            var zero = ElementValue(map) switch { "bool" => "false", "Ref" => "null", _ => "0" };
                            // (a struct's array: each cell the struct's default value)
                            var element = ((IArrayTypeSymbol)n.ArrayType).ElementType;
                            stmts.Add(MMapUpdate.Of(
                                map,
                                t,
                                IsStruct(element) ? MapLambda("j: int", MathTypes.StructDefault(element))
                                                                         : IsFloating(element) ? MapLambda("j: int", MathTypes.FloatLiteral(0.0, element))
                                                                         : new MLit($"(lambda j: int :: {zero})")));
                            if (n.Elements != null)
                            {
                                for (int k = 0; k < n.Elements.Length; k++)
                                {
                                    stmts.Add(MMapUpdate.Of(map, t, index: new MLit(k.ToString()), value: n.Elements[k]));
                                }
                            }
                            break;
                        }
                        case MLambda lam:
                            // (a new reference: no other delegate's facts are its)
                            p.Source.AddModifies("$Alloc");
                            p.Source.AddAnyWrite("$Alloc");
                            Allocate(stmts, lam.Var);
                            stmts.Add(lam);
                            break;
                        case IHeapStmt same:
                            stmts.Add(same);
                            break;
                        default: throw new System.InvalidOperationException("a level 2 statement Heap doesn't know: " + s.GetType().Name);
                    }
                }
                return stmts;
            }
        }

        /// <summary>
        /// Each loop that writes arrays only through variables it doesn't change:
        /// a frame at its head, and a snapshot on each way in. A write through anything else keeps nothing. What a loop
        /// writes is read from level 2's blocks (its stores, allocations, calls); the frames go into level 3's, first in
        /// its head and last in each block into it.
        /// </summary>
        private static void LoopFrames(MProcedure p, HProcedure h)
        {
            foreach (var (head, last) in p.Source.LoopBodies)
            {
                var body = p.Blocks.Where(b => b.Ordinal >= head && b.Ordinal <= last).ToList();
                var assigned = new HashSet<string>(body.SelectMany(b => b.Stmts).Select(s => s switch
                {
                    MAssign a => a.Var, MCall c => c.Result, MInvoke iv => iv.Result, MLambda lam => lam.Var, MNew n => n.Var, MNewObj o => o.Var, MHavoc h => h.Var, _ => null,
                }).Where(x => x != null));
                var frame = new HLoopFrame { Head = head };
                bool keeps = true;
                foreach (var s in body.SelectMany(b => b.Stmts))
                {
                    switch (s)
                    {
                        case MStore st when st.Array is MVar v && !assigned.Contains(v.Name):
                            if (!frame.Writers.Any(w => ((MVar)w).Name == v.Name))
                            {
                                frame.AddWriter(v);
                            }
                            break;
                        case MStore _:
                            keeps = false;
                            break;
                        case MInvoke _: case MHavocAll _: case MAwait _:
                            keeps = false;
                            break; // (a delegate, or unknown code, may write any array) // (a delegate, or unknown code, may write any array)
                        case MCall c:
                            frame.AddCallee(c.Callee);
                            break;
                        case MNewObj o when o.Ctor != null:
                            frame.AddCallee(o.Ctor);
                            break;
                    }
                }
                var entry = p.Blocks.FirstOrDefault(b => b.Label == $"b{head}");
                var hEntry = h.Blocks.FirstOrDefault(b => b.Label == $"b{head}");
                var hInto = h.Blocks.Where(b => b.Ordinal < head && b.Jump is KGoto g && g.Targets.Contains($"b{head}")).ToList();
                // (a loop that awaits or calls what may change anything: the confined objects it doesn't reassign still
                // hold what they held, but what it writes through them)
                var confined = p.Source.Confined.Where(c => !assigned.Contains(c)).ToList();
                if (entry != null && confined.Count > 0)
                {
                    var cf = new HConfinedFrame { Head = head };
                    foreach (var c in confined)
                    {
                        cf.Locals[c] = new HashSet<string>();
                    }
                    foreach (var st in body.SelectMany(b => b.Stmts))
                    {
                        switch (st)
                        {
                            case MStore ks when ks.Array is MVar kv && cf.Locals.ContainsKey(kv.Name):
                                cf.Locals[kv.Name].Add(Elements(ks.ArrayType));
                                break;
                            case MFieldStore kf when kf.Instance is MVar fv && cf.Locals.ContainsKey(fv.Name):
                                cf.Locals[fv.Name].Add(FieldMap(kf.Field));
                                break;
                            case MCall kc when kc.Receiver is MVar rv && cf.Locals.ContainsKey(rv.Name):
                                cf.Locals[rv.Name].Add("$M.");
                                break;
                            case MCall kc2:
                                foreach (var a in kc2.Args.OfType<MVar>().Where(a => cf.Locals.ContainsKey(a.Name)))
                                {
                                    cf.RemoveLocal(a.Name);
                                }
                                break;
                        }
                    }
                    if (cf.Locals.Count > 0)
                    {
                        hEntry.InsertStmt(0, cf);
                        foreach (var b in hInto)
                        {
                            b.AddStmt(new HConfinedSnapshot { Head = head });
                        }
                    }
                }
                // (the atomic fields at the loop's head: steps since the loop was entered, of a snapshot taken on the way in)
                if (entry?.Stmts.OfType<MAtomicSteps>().FirstOrDefault() is MAtomicSteps steps && steps.Head < 0)
                {
                    var atomic = p.Source.Fields.Where(f => Atomics.IsAtomic(f) && Atomics.StepOf(f) != null && IsField(f)).Select(f => (map: FieldMap(f), type: TypeOf(FieldType(f)))).Distinct().ToList();
                    var into = hInto;
                    if (atomic.Count > 0 && into.Count > 0)
                    {
                        steps.Head = head;
                        p.Source.AddLocal(KLocal.Of($"as{head}$Alloc", "[Ref]bool"));
                        foreach (var (map, type) in atomic)
                        {
                            steps.AddMap(map);
                            p.Source.AddLocal(KLocal.Of($"as{head}{map}", "[Ref]" + type));
                        }
                        foreach (var b in into)
                        {
                            b.AddStmt(MAssign.Of($"as{head}$Alloc", new MVar("$Alloc")));
                            foreach (var (map, _) in atomic)
                            {
                                b.AddStmt(MAssign.Of($"as{head}{map}", new MVar(map)));
                            }
                        }
                    }
                }
                if (!keeps || entry == null)
                {
                    continue;
                }
                hEntry.InsertStmt(0, frame);
                foreach (var b in hInto)
                {
                    b.AddStmt(new HSnapshot { Frame = frame });
                }
            }
        }

        private static bool HasInitializer(ISymbol field) =>
            field.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).Any(s =>
                s is Microsoft.CodeAnalysis.CSharp.Syntax.VariableDeclaratorSyntax v && v.Initializer != null ||
                s is Microsoft.CodeAnalysis.CSharp.Syntax.PropertyDeclarationSyntax pd && pd.Initializer != null);
    }
}
