using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.MOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Cells: array cells and memory views as permissions; the cell modes.</summary>
    internal sealed partial class Checks
    {
        /// <summary>Is cell (x, i) among c's, where g holds?</summary>
        internal static MExpr InCells(MExpr g, MCells c, MExpr x, MExpr i) =>
            Conj(g, AndAlso(AndAlso(Eq(x, c.Arr), new MOp("<=", c.Lo, i)), new MOp("<", i, c.Hi)));

        private static MExpr Cell(MExpr x, MExpr i) => Sel("cells", x, i);

        private void ChangeCells(MExpr g, MCells c, string op)
        {
            var (x, i) = (new MVar("x$"), new MVar("i$"));
            Emit(new MAssign
            {
                Var = "cells",
                Value = new MOp("lambda", new MLit("x$: Ref"), new MOp("lambda", new MLit("i$: int"),
                Ite(InCells(g, c, x, i), new MOp(op, Cell(x, i), Amount(c.Read)), Cell(x, i)))),
            });
        }

        /// <summary>The first cells of the memory views granted so far: where a new one's room is said too.</summary>
        private readonly List<MExpr> _memLos = new List<MExpr>();

        private void InhaleCells(MExpr g, MCells c)
        {
            // two whole permissions to one cell can't both be in hand (a method that holds every cell learns nothing)
            if (_p.ArrayMode)
            {
                var i = new MVar("i$");
                var room = c.Read ? new MOp("<=", Cell(c.Arr, i), new MLit("1.0 - " + Share)) : new MOp("<", Cell(c.Arr, i), MLit.FullPermission);
                Assume(MQuant.ForAll("i$", Implies(InCells(g, c, c.Arr, i), room)));
                var lo = c.Read ? new MOp("<=", Cell(c.Arr, c.Lo), new MLit("1.0 - " + Share)) : new MOp("<", Cell(c.Arr, c.Lo), MLit.FullPermission);
                Assume(Implies(InCells(g, c, c.Arr, c.Lo), lo));
                // (memory: two intervals overlap only where one starts inside the other, so at the other views' first cells too)
                if (c.Arr is MLit { Text: "null" })
                {
                    foreach (var other in _memLos)
                    {
                        Assume(Implies(InCells(g, c, c.Arr, other), c.Read ? new MOp("<=", Cell(c.Arr, other), new MLit("1.0 - " + Share)) : new MOp("<", Cell(c.Arr, other), MLit.FullPermission)));
                    }
                    _memLos.Add(c.Lo);
                }
            }
            ChangeCells(g, c, "+");
        }

        private void ExhaleCells(MExpr g, MCells c, SyntaxNode at, string message)
        {
            var i = new MVar("i$");
            Assert(MQuant.ForAll("i$", Implies(InCells(g, c, c.Arr, i), new MOp(">=", Cell(c.Arr, i), Amount(c.Read)))), At("CSV1016", at, message));
            ChangeCells(g, c, "-");
        }

        /// <summary>
        /// The cell modes, decided from the lowered body and its callees' signatures before anything reads them. A method
        /// whose contract names cells holds none but those it gets (array mode); one that exchanges some (a call, a fold)
        /// keeps them; any other holds every cell, which nothing then changes.
        /// </summary>
        private void DecideCellModes()
        {
            if (_program.UsesPermissions)
            {
                var stmts = _p.Blocks.SelectMany(b => b.Stmts).ToList();
                bool foldsCells = stmts.OfType<KFold>().Any(f => PredicateHasCells(f.Inst.Pred));
                bool callsCells(Func<KProcedure, IEnumerable<KExpr>> specs) => stmts.OfType<KCall>().Any(c => !_program.ContractOf(c.Callee).IsPure && NamesCells(specs(_program.Signature(c.Callee))));
                _p.ArrayMode = _p.MemViews || NamesCells(_rawRequires.Concat(_rawEnsures)) || foldsCells ||
                               callsCells(sig => sig.Ensures.Select(e => e.Expr).SelectMany(x => x.Atoms()).OfType<KInst>().Where(q => PredicateHasCells(q.Pred)));
                _p.UsesCells = _p.ArrayMode || callsCells(sig => sig.Requires.Concat(sig.Ensures).Select(x => x.Expr));
                if (_p.UsesCells)
                {
                    _p.UsesPerm = true;
                }
            }
            _p.UsesFields = _p.UsesPerm && _program.UsesFieldPermissions;
        }

        private bool PredicateHasCells(IMethodSymbol pred, HashSet<IMethodSymbol> seen = null)
        {
            seen ??= new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
            if (!seen.Add(pred))
            {
                return false;
            }
            var body = _program.Signature(pred).FunctionBody;
            return body != null && body.Atoms().Any(a => a is KCells || a is KInst q && PredicateHasCells(q.Pred, seen));
        }

        /// <summary>Do these specifications name cells (directly, or in a predicate that holds some)?</summary>
        private bool NamesCells(IEnumerable<KExpr> specs) => specs.SelectMany(x => x.Atoms()).Any(a => a is KCells || a is KInst q && PredicateHasCells(q.Pred));
    }
}
