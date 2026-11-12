using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.FlowAnalysis;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Exceptions. An exception is an object (not null, of the type thrown) whose dynamic type the handlers test:
    /// <list type="bullet">
    /// <item>it is raised by <c>throw</c>, by a call (any callee may throw anything: methods are verified for partial
    /// correctness; its Spec.EnsuresOnThrow says what then holds), and by operations that throw (checked overflow,
    /// a failed cast, Math.Abs(MinValue));</item>
    /// <item>the enclosing try regions are searched: a catch whose type it is an instance of (and whose filter holds)
    /// handles it; a finally runs on the way, then the search goes on; leaving the method, its own
    /// Spec.EnsuresOnThrow clauses must hold;</item>
    /// <item>a call that throws gives nothing back: views lent by ref are lost, invariants and postconditions are
    /// not known (only its exceptional postconditions);</item>
    /// <item>a finally also runs on every normal way out of its try (a continuation on the path, Frame.Pending).</item>
    /// </list>
    /// An exceptional path is explored only where something sees it (a try around, or exceptional postconditions):
    /// elsewhere a throw just ends the path, as before. Proofs (lemmas, [Pure]) may not throw at all.
    /// </summary>
    internal sealed partial class StaticChecks
    {
    }
}
