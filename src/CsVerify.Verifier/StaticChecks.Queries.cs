using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// LINQ, read from its definitions: each System.Linq.Enumerable member (and List's predicate methods) is defined
    /// by a [Comprehensions] method of the Spec library (Bcl/Linq.cs), written with CsVerify.Q, and a call is read by
    /// running that definition here, symbolically, on what the call was given.
    ///
    /// A definition's comprehension (Q.For, Q.If, Q.Yield) is put into the normal form of Cheney, Lindley and Wadler's
    /// "A Practical Theory of Language-Integrated Query" (ICFP 2013): a source is never itself a comprehension
    /// (for-yield, for-for, for-if), and conditions in a row are one (if-if); their union rule, which reorders, is not
    /// used, so the order is LINQ to Objects'. The normal form, "for each x1 of s1, each x2 of s2(x1), ..., if c, yield
    /// v", is compiled into the primitives (StaticChecks.Linq): sources one after another for each For, a filter for
    /// the If, and the yielded values. Lengths, elements, ranges, folds, sorts and groups are the primitives' own.
    ///
    /// A member returning a sequence is a query: its result is a term standing for the call, read (its definition
    /// run) when it is enumerated, on its sources and its lambdas' captures as they are then. Any other member is read
    /// at the call: its Spec.Requires are proved there (the member throws where they do not hold), and its value is
    /// its body's. Lambdas are inlined where they are pure (PureLambdaBody); with another, or a source the verifier
    /// cannot read, the call is a library call without a contract, as is a query whose definition this cannot read
    /// (a sequence made anew for each element: groups read inside another lambda).
    /// </summary>
    internal sealed partial class StaticChecks
    {
        private int _queryIds, _boundCompile;
    }
}
