using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Atomic fields (<see cref="Atomics"/>). A field map's value at an atomic field is what this thread last saw or wrote
    /// there; specifications speak of that. A read in code first lets the others take steps (a fresh value, the same or a
    /// step on), and a write is proved a step from the value it replaces, which the others may also have moved: so a plain
    /// <c>x = x + 1</c> isn't one, and only <c>Interlocked</c> reads and writes in one step.
    /// </summary>
    internal sealed partial class StaticChecks
    {
        private const string AtomicId = "CSV1030";

        private void CheckAtomics()
        {
            foreach (var (at, message) in _engine.Atomics.Misdeclared(_engine.Fields, _engine.Locks))
                if (_engine.Atomics.Claim(at)) Report(AtomicId, at, message, isError: true);
            // (a step's transitivity: Boogie's, Lowering)
        }
    }
}
