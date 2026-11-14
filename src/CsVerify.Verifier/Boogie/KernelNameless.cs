using System;
using System.Collections.Generic;
using System.Linq;

namespace CsVerify.Verifier.Boogie
{
    // Locally nameless terms (Charguéraud): a bound variable is a De Bruijn index (KBound), a free one a name. A binder's
    // body is made of a name (a fresh atom, ln$n, in the LINQ and EF lowering) and closed over it, the name becoming an
    // index; a template (KAbs) is instantiated by opening it at locally closed terms; a pass that goes under a binder
    // opens it at a fresh name. None of them can capture. Where a term leaves the LINQ lowering, an index left dangling,
    // or an atom left free, is an error (Leaving); names are the printer's alone.

    /// <summary>A bound variable: of the index-th binder out from here (0, the nearest).</summary>
    internal sealed class KBound : KExpr
    {
        public readonly int Index;

        public KBound(int index)
        {
            Index = index;
        }
    }

    /// <summary>A term over its Arity variables (indices 0 to Arity - 1 at its top, the first 0).</summary>
    internal sealed class KAbs
    {
        public readonly int Arity;
        public readonly KExpr Body;

        private KAbs(int arity, KExpr body)
        {
            Arity = arity;
            Body = body;
        }

        /// <summary>The term over one variable that body is of the atom.</summary>
        public static KAbs Of(KVar atom, KExpr body) => new KAbs(1, Nameless.Close(body, atom));

        /// <summary>The term over two variables that body is of the atoms (a0's index 0).</summary>
        public static KAbs Of(KVar a0, KVar a1, KExpr body) => new KAbs(2, Nameless.Close(body, a0, a1));

        /// <summary>The term at these (locally closed) arguments, one for each of its variables.</summary>
        public KExpr At(params KExpr[] args)
        {
            if (args.Length != Arity)
            {
                throw new InvalidOperationException($"a term over {Arity} variables opened at {args.Length}");
            }
            return Nameless.Open(Body, args);
        }

        /// <summary>This term with a free atom given a (locally closed) value.</summary>
        public KAbs With(KVar atom, KExpr value) => new KAbs(Arity, Nameless.Substitute(Body, atom, value));
    }

    /// <summary>
    /// A rewrite of kernel expressions: each node rebuilt of its parts rewritten (a literal, a variable or an index kept),
    /// unless an override says otherwise. Binders: a quantifier's parts are visited one level deeper (Depth); a let's at
    /// the same (it binds a name, not an index). Any other kind is an error.
    /// </summary>
    internal abstract class KRewriter
    {
        protected int Depth;

        public KExpr Visit(KExpr e) => e switch
        {
            null => null,
            KBound b => VisitBound(b),
            KVar v => VisitVar(v),
            KLit => e,
            KQuant q => VisitQuant(q),
            _ => Rebuild(e),
        };

        protected virtual KExpr VisitBound(KBound b) => b;

        protected virtual KExpr VisitVar(KVar v) => v;

        protected virtual KExpr VisitQuant(KQuant q)
        {
            Depth++;
            try
            {
                return q.WithParts(Visit(q.Range), Visit(q.Body), All(q.Trigger));
            }
            finally
            {
                Depth--;
            }
        }

        protected KExpr[] All(KExpr[] es) => es?.Select(Visit).ToArray();

        private KExpr Rebuild(KExpr e) => e switch
        {
            KOp op => new KOp(op.Op, All(op.Args)),
            KFnApp f => f.WithArgs(All(f.Args), Visit(f.Snap)),
            KLet l => KLet.Of(l.Var, Visit(l.Value), Visit(l.Body)),
            KArith a => new KArith
            {
                Op = a.Op,
                Left = Visit(a.Left),
                Right = Visit(a.Right),
                Type = a.Type,
                Mode = a.Mode,
                At = a.At,
                ThrowsTo = a.ThrowsTo,
            },
            KConv c => new KConv
            {
                Value = Visit(c.Value),
                From = c.From,
                To = c.To,
                Mode = c.Mode,
                At = c.At,
            },
            KIfc i => new KIfc
            {
                Item = i.Item,
                Of = Visit(i.Of),
                Index = Visit(i.Index),
                Element = i.Element,
                Fresh = i.Fresh,
                At = i.At,
                OfAt = i.OfAt,
            },
            KMultiset ms => new KMultiset
            {
                Array = Visit(ms.Array),
                Count = Visit(ms.Count),
                ArrayType = ms.ArrayType,
                Levels = ms.Levels,
                At = ms.At,
            },
            KElem el => new KElem
            {
                String = el.String,
                Model = el.Model,
                Domain = el.Domain,
                Array = Visit(el.Array),
                Index = Visit(el.Index),
                ArrayType = el.ArrayType,
                InSpec = el.InSpec,
                Unchecked = el.Unchecked,
                NoNull = el.NoNull,
                Alongside = Visit(el.Alongside),
                At = el.At,
                ArrayAt = el.ArrayAt,
            },
            KLen len => new KLen
            {
                String = len.String,
                Array = Visit(len.Array),
                InSpec = len.InSpec,
                At = len.At,
                ArrayAt = len.ArrayAt,
            },
            KFnCall fc => new KFnCall
            {
                Callee = fc.Callee,
                Receiver = Visit(fc.Receiver),
                ReceiverIsThis = fc.ReceiverIsThis,
                Args = All(fc.Args),
                At = fc.At,
                ReceiverAt = fc.ReceiverAt,
                Stub = fc.Stub,
            },
            KField fd => new KField
            {
                Field = fd.Field,
                Instance = Visit(fd.Instance),
                OnThis = fd.OnThis,
                NoNull = fd.NoNull,
                At = fd.At,
                InstanceAt = fd.InstanceAt,
            },
            KAcc acc => new KAcc
            {
                Obj = Visit(acc.Obj),
                Type = acc.Type,
                At = acc.At,
            },
            KCells cl => new KCells
            {
                Arr = Visit(cl.Arr),
                Lo = Visit(cl.Lo),
                Hi = Visit(cl.Hi),
                Read = cl.Read,
                At = cl.At,
            },
            KFieldAcc fa => new KFieldAcc
            {
                Obj = Visit(fa.Obj),
                Field = fa.Field,
                Type = fa.Type,
                At = fa.At,
            },
            KInst inst => new KInst
            {
                Pred = inst.Pred,
                Args = All(inst.Args),
                At = inst.At,
            },
            KDataField df => new KDataField
            {
                Function = df.Function,
                Value = Visit(df.Value),
                At = df.At,
                ValueAt = df.ValueAt,
                Struct = df.Struct,
            },
            KCast cast => new KCast
            {
                Value = Visit(cast.Value),
                Test = Visit(cast.Test),
                At = cast.At,
            },
            _ => throw new InvalidOperationException("a kernel expression the rewrite doesn't know: " + e.GetType().Name),
        };
    }

    /// <summary>Opening, closing, substituting and naming locally nameless terms.</summary>
    internal static class Nameless
    {
        /// <summary>An atom's name: of this prefix, and nowhere else.</summary>
        public const string AtomPrefix = "ln$";

        /// <summary>body's indices 0 to args.Length - 1 at its top replaced by args (each locally closed).</summary>
        public static KExpr Open(KExpr body, KExpr[] args)
        {
            foreach (var a in args)
            {
                LocallyClosed(a);
            }
            return new Opener(args).Visit(body);
        }

        /// <summary>body with each atom an index at its top (atoms[0] index 0).</summary>
        public static KExpr Close(KExpr body, params KVar[] atoms)
        {
            foreach (var a in atoms)
            {
                if (!a.Name.StartsWith(AtomPrefix))
                {
                    throw new InvalidOperationException("closing over a name that is no atom: " + a.Name);
                }
            }
            return new Closer(atoms.Select(a => a.Name).ToArray()).Visit(body);
        }

        /// <summary>body with a variable's name an index at its top (a quantifier made of a named variable's body).</summary>
        public static KExpr CloseName(KExpr body, string name) => new Closer(new[] { name }).Visit(body);

        /// <summary>body with a free atom given a (locally closed) value.</summary>
        public static KExpr Substitute(KExpr body, KVar atom, KExpr value)
        {
            LocallyClosed(value);
            return new Substituter(atom.Name, value).Visit(body);
        }

        /// <summary>A term as it leaves the lowering of queries: no index dangling, no atom free in it (an error otherwise).</summary>
        public static KExpr Leaving(KExpr e)
        {
            new LeavingCheck().Visit(e);
            return e;
        }

        /// <summary>A term no index of which is dangling (an error otherwise).</summary>
        public static void LocallyClosed(KExpr e) => new ClosedCheck().Visit(e);

        private sealed class Opener : KRewriter
        {
            private readonly KExpr[] _args;

            public Opener(KExpr[] args)
            {
                _args = args;
            }

            protected override KExpr VisitBound(KBound b)
            {
                var k = b.Index - Depth;
                if (k < 0)
                {
                    return b;
                }
                if (k >= _args.Length)
                {
                    throw new InvalidOperationException($"a dangling index: {b.Index} at depth {Depth}, of {_args.Length} variables");
                }
                return _args[k];
            }
        }

        private sealed class Closer : KRewriter
        {
            private readonly string[] _atoms;

            public Closer(string[] atoms)
            {
                _atoms = atoms;
            }

            protected override KExpr VisitVar(KVar v)
            {
                var k = Array.IndexOf(_atoms, v.Name);
                return k < 0 ? v : new KBound(Depth + k);
            }
        }

        private sealed class Substituter : KRewriter
        {
            private readonly string _atom;
            private readonly KExpr _value;

            public Substituter(string atom, KExpr value)
            {
                _atom = atom;
                _value = value;
            }

            protected override KExpr VisitVar(KVar v) => v.Name == _atom ? _value : v;
        }

        private sealed class ClosedCheck : KRewriter
        {
            protected override KExpr VisitBound(KBound b)
            {
                if (b.Index >= Depth)
                {
                    throw new InvalidOperationException($"a dangling index: {b.Index} at depth {Depth}");
                }
                return b;
            }
        }

        private sealed class LeavingCheck : KRewriter
        {
            protected override KExpr VisitBound(KBound b) =>
                b.Index >= Depth ? throw new InvalidOperationException($"a dangling index where a term leaves the lowering: {b.Index} at depth {Depth}") : b;

            protected override KExpr VisitVar(KVar v) =>
                v.Name.StartsWith(AtomPrefix) ? throw new InvalidOperationException("an atom where a term leaves the lowering: " + v.Name) : v;
        }
    }
}
