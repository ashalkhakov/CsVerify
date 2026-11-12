using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Facts about loops without invariants, inferred as Houdini does. Candidates come from the loop's condition
    /// (<c>i &lt; n</c> suggests <c>i &lt;= n</c> at the head) and from the integers it changes (each may never go below,
    /// or never above, its value on entry). A candidate that holds on entry is assumed at the head. Each back edge
    /// checks it again; if it might not hold there, the method is verified again without it, until every candidate
    /// assumed is one that held at every back edge (<see cref="FailedLoopFacts"/>, Engine's reruns). Loops with
    /// invariants of their own are left as they are.
    /// </summary>
    internal sealed partial class StaticChecks
    {

        private readonly ISet<string> _excludedFacts;
    }
}
