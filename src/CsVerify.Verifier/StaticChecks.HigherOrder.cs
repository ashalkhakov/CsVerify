using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// What a delegate without a contract (a Func, an Action, a delegate type with no [ContractClassFor]) accepts and
    /// gives, as Dafny's <c>f.requires</c> and <c>f.ensures</c>: <c>Spec.Pre(f, x)</c> and <c>Spec.Post(f, x, r)</c>,
    /// functions of the delegate value and its arguments, the same in every state; <c>Spec.Total(f)</c> is Spec.Pre
    /// for every argument.
    /// <list type="bullet">
    /// <item>A call <c>f(x)</c> proves <c>Spec.Pre(f, x)</c> and gives a result r with <c>Spec.Post(f, x, r)</c>.</item>
    /// <item>No delegate is taken to be total: what one from a parameter, a field or a call accepts is what a
    /// specification says, and nothing otherwise, as in ATS.</item>
    /// <item>A lambda made a delegate defines them: its Spec.Pre is its own Spec.Requires (total without one, since its
    /// body is proved for every argument), and its Spec.Post implies what it ensures and, for an expression, its value.
    /// Both are taken only as far as they depend on its parameters and on captured variables that never change; a
    /// precondition that depends on more can't be a Spec.Pre, so it is reported (CSV1029). A method group made one
    /// gives its method's contract the same way.</item>
    /// <item>A delegate handed to a library (Task.Run, List.ForEach, a query) may be called with anything, so it must
    /// be total (CSV1029).</item>
    /// <item>A lambda knows the preconditions of the method it is in that are of what never changes (Spec.Total of a
    /// parameter never assigned): they held when it was made and still do.</item>
    /// </list>
    /// </summary>
    internal sealed partial class StaticChecks
    {
    }
}
