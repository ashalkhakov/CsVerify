namespace CsVerify
{
    using System;

    /// <summary>
    /// Values of this type are linear (ATS views / <c>viewtype</c>): every one must be consumed exactly once on every
    /// path, cannot be copied, boxed, captured by lambdas or stored in non-linear types. <c>ref</c>/<c>in</c> borrow.
    /// </summary>
    [AttributeUsage(AttributeTargets.Struct | AttributeTargets.Class, Inherited = true)]
    public sealed class LinearAttribute : Attribute { }

    /// <summary>
    /// A proof function (ATS <c>prfun</c>): must be <c>void</c> and <c>[Conditional("CSVERIFY_SPEC")]</c>, so calls are
    /// erased. Its body is the proof; callers gain its postconditions.
    /// </summary>
    [AttributeUsage(AttributeTargets.Method)]
    public sealed class LemmaAttribute : Attribute { }

    /// <summary>
    /// Trusted code (ATS <c>$UNSAFE</c>): the verifier assumes the contract without checking the body, and the
    /// analyzers skip linearity checks inside it.
    /// </summary>
    [AttributeUsage(AttributeTargets.Method | AttributeTargets.Constructor | AttributeTargets.Class | AttributeTargets.Struct)]
    public sealed class TrustedAttribute : Attribute { }

    /// <summary>
    /// A specification-only function (ATS static function): pure, callable only from specifications, and its body
    /// is ghost context, so it may use quantifiers, <see cref="Seq{T}"/> and <c>Ghost.Value</c>.
    /// </summary>
    [AttributeUsage(AttributeTargets.Method)]
    public sealed class GhostFunctionAttribute : Attribute { }

    /// <summary>
    /// A side-effect-free function usable inside specifications. The verifier treats it as a mathematical function
    /// and unfolds a single-<c>return</c> body once at every use.
    /// </summary>
    [AttributeUsage(AttributeTargets.Method)]
    public sealed class PureAttribute : Attribute { }

    /// <summary>
    /// An object invariant: a [Pure] parameterless bool method of an immutable positional record. It is proved at
    /// every construction (<c>new</c>) and assumed of every object of the type, which can never change afterwards.
    /// </summary>
    [AttributeUsage(AttributeTargets.Method)]
    public sealed class InvariantAttribute : Attribute { }

    /// <summary>
    /// A class whose objects are owned through a linear <see cref="Own{T}"/> view (ATS style): only code holding the
    /// view may write their fields, and the class's [Invariant] travels with the view.
    /// </summary>
    [AttributeUsage(AttributeTargets.Class)]
    public sealed class OwnedAttribute : Attribute { }

    /// <summary>
    /// A field of an [Owned] class that owns the object it refers to: that object's view is inside the container,
    /// so only code holding the container can get at it (with Own.Take / Own.Give), and the container's invariant
    /// may read its fields. Ownership forms trees (ATS's nested views).
    /// </summary>
    [AttributeUsage(AttributeTargets.Field)]
    public sealed class OwnsAttribute : Attribute { }

    /// <summary>
    /// Marks a class whose methods hold the specifications of an interface's or abstract class's members, which have
    /// no body to write them in (the .NET Code Contracts pattern): the class implements the interface (or derives
    /// from the abstract class), and each method's leading Spec.Requires/Ensures/Modifies/Reads statements are that
    /// member's contract. Its bodies are never run or verified; the erasure pass removes the class.
    /// </summary>
    [AttributeUsage(AttributeTargets.Class)]
    public sealed class ContractClassForAttribute : Attribute
    {
        public ContractClassForAttribute(Type type) { Type = type; }
        public Type Type { get; }
    }
}
