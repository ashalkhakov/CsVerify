using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Entity Framework Core (EfModel has the model). A query on a context's DbSet is LINQ over the table as it is when
    /// the query runs: a sequence in no order the database promises, whose rows have distinct keys (and distinct values
    /// of each unique index) and pass the entity's query filters. Queryable's operators and EF's ...Async forms are read
    /// from LINQ to Objects' definitions over it.
    /// </summary>
    internal partial class StaticChecks
    {

        private EfModel Ef => _engine.Ef;

        private static bool IsEfMethod(IMethodSymbol m) =>
            m.ContainingNamespace?.ToDisplayString() is string ns && (ns == "Microsoft.EntityFrameworkCore" || ns.StartsWith("Microsoft.EntityFrameworkCore."));

        internal const string CollationTheory =
            "(declare-fun cv_collate (Int Int) Bool)\n" +
            "(assert (forall ((x Int)) (! (cv_collate x x) :pattern ((cv_collate x x)))))\n" +
            "(assert (forall ((x Int) (y Int)) (! (=> (cv_collate x y) (cv_collate y x)) :pattern ((cv_collate x y)))))\n" +
            "(assert (forall ((x Int) (y Int) (z Int)) (! (=> (and (cv_collate x y) (cv_collate y z)) (cv_collate x z)) :pattern ((cv_collate x y) (cv_collate y z)))))";

        internal const string OrderId = "CSV1031", TranslateId = "CSV1032";
    }
}
