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
    /// Objects of this class hold a resource and must be disposed: each one created (or returned by a call) is disposed
    /// exactly once on every path (<c>Dispose()</c>, <c>using</c>), not used after, or handed over (returned, stored in
    /// a field, passed to a <see cref="TakesOwnershipAttribute"/> parameter, <see cref="Spec.HandOver"/>). On a
    /// [ContractsFor] stub class, it marks the library type the stub is for (FileStream). A class with a field of such
    /// a type owns it: it must be IDisposable, its Dispose must dispose the field, and it must be disposed itself.
    /// </summary>
    [AttributeUsage(AttributeTargets.Class, Inherited = true)]
    public sealed class MustDisposeAttribute : Attribute { }

    /// <summary>A parameter that takes the disposable it is handed: its caller need not (and must not) dispose it.</summary>
    [AttributeUsage(AttributeTargets.Parameter)]
    public sealed class TakesOwnershipAttribute : Attribute { }

    /// <summary>A field of a disposable type that its object does not own (someone else disposes it).</summary>
    [AttributeUsage(AttributeTargets.Field | AttributeTargets.Property)]
    public sealed class NotOwnedAttribute : Attribute { }

    /// <summary>
    /// What a lock protects. On a field or auto-property: it may be used only while holding the lock, a readonly field of
    /// this class (CSV1023). On a method: its caller must hold it, and the method may use what it guards. A field written
    /// under one lock, and no other, is taken to be guarded by it without this.
    /// </summary>
    [AttributeUsage(AttributeTargets.Field | AttributeTargets.Property | AttributeTargets.Method)]
    public sealed class GuardedByAttribute : Attribute
    {
        public GuardedByAttribute(string lockField) { LockField = lockField; }
        public string LockField { get; }
    }

    /// <summary>
    /// A <c>[Pure]</c> or <c>[GhostFunction]</c> bool method that holds while a lock is free: known on entering it, and to be
    /// restored on leaving it and before a call that may enter it again (CSV1024). It may read what the lock guards.
    /// </summary>
    [AttributeUsage(AttributeTargets.Method)]
    public sealed class LockInvariantAttribute : Attribute
    {
        public LockInvariantAttribute(string lockField) { LockField = lockField; }
        public string LockField { get; }
    }

    /// <summary>
    /// A method (or every method of a class) that the program's callers run at the same time, as a web framework does with
    /// its handlers. Like code a task runs, it must hold a lock or a permission for every field and array cell it uses.
    /// </summary>
    [AttributeUsage(AttributeTargets.Method | AttributeTargets.Class)]
    public sealed class RunsConcurrentlyAttribute : Attribute { }

    /// <summary>
    /// A method that takes a lock for its caller, wrapping a <c>SemaphoreSlim</c> of count 1 (Clang's ACQUIRE, or its scoped
    /// capability). The lock is the field the call is on (<c>_lock.LockAsync()</c>, an instance method of a lock class or an
    /// extension of SemaphoreSlim), or the field named here, of the object the method is called on (<c>EnterAsync()</c>).
    /// If it returns something disposable, disposing that gives the lock back, and it is used in a <c>using</c>:
    /// <c>using (await _lock.LockAsync()) { ... }</c>. If not, it's as for the semaphore's own Wait:
    /// <c>await EnterAsync(); try { ... } finally { Exit(); }</c>. That the method does this is taken from its shape, not
    /// proved: it must call Wait or WaitAsync, and its result's Dispose Release. On a [ContractsFor] stub, it says so of a
    /// library's lock, which is taken on trust.
    /// </summary>
    [AttributeUsage(AttributeTargets.Method)]
    public sealed class AcquiresAttribute : Attribute
    {
        public AcquiresAttribute() { }
        public AcquiresAttribute(string lockField) { LockField = lockField; }
        public string LockField { get; }
    }

    /// <summary>A method that gives back the lock an <see cref="AcquiresAttribute"/> method took: the field the call is on, or the one named here.</summary>
    [AttributeUsage(AttributeTargets.Method)]
    public sealed class ReleasesAttribute : Attribute
    {
        public ReleasesAttribute() { }
        public ReleasesAttribute(string lockField) { LockField = lockField; }
        public string LockField { get; }
    }

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
    /// A predicate (Viper's, or ATS's dataview): a static bool method whose body, one expression, describes a
    /// footprint of permissions (<see cref="Spec.Acc(object)"/>, other predicates, conjoined with <c>&amp;&amp;</c> or in the branches
    /// of <c>?:</c>) and facts about it. Holding an instance <c>P(args)</c> holds those permissions, folded:
    /// <see cref="Spec.Unfold"/> trades it for its body, <see cref="Spec.Fold"/> back. Specification only; never
    /// unfolded on its own, so it may be recursive.
    /// </summary>
    [AttributeUsage(AttributeTargets.Method)]
    public sealed class PredicateAttribute : Attribute { }

    /// <summary>
    /// A side-effect-free function usable inside specifications. The verifier treats it as a mathematical function
    /// and unfolds a single-<c>return</c> body once at every use.
    /// </summary>
    [AttributeUsage(AttributeTargets.Method | AttributeTargets.Property)]
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

    /// <summary>
    /// Marks a stub: a class that gives contracts to the members of a type whose sources the program does not have
    /// (the BCL, a third-party assembly). Its methods match the external type's members by signature, and each one's
    /// leading Spec.Requires/Ensures/EnsuresOnThrow/Modifies statements are that member's contract:
    /// <list type="bullet">
    /// <item>a static method matches the static method of the same name and parameters;</item>
    /// <item>a static method whose first parameter is named <c>@this</c>, of the external type, matches the instance
    /// method of that name taking the other parameters (<c>@this</c> is the receiver);</item>
    /// <item>property accessors are methods named <c>get_P</c> and <c>set_P</c> (an indexer's are <c>get_Item</c> and
    /// <c>set_Item</c>); a getter may also be named <c>P</c>;</item>
    /// <item>a static method named <c>@new</c>, returning the external type, matches the constructor with its parameters.</item>
    /// </list>
    /// A generic stub (<c>[ContractsFor(typeof(List&lt;&gt;))] class ListContracts&lt;T&gt;</c>) has the type's type
    /// parameters, in order. The contracts are trusted: they are assumed at calls, never proved, so a wrong one makes
    /// wrong things provable (the verifier counts the ones it used). A stub's preconditions are proved at every call;
    /// without Spec.Modifies, a member changes no [Model] state. Its bodies are never run or verified; the erasure
    /// pass removes the class.
    /// </summary>
    [AttributeUsage(AttributeTargets.Class)]
    public sealed class ContractsForAttribute : Attribute
    {
        public ContractsForAttribute(Type type) { Type = type; }
        public Type Type { get; }
    }

    /// <summary>
    /// On a [ContractsFor] class: its methods define their members as comprehensions (<see cref="Q"/>) rather than
    /// specify them with contracts. The verifier reads each body as the member's meaning: a member returning a
    /// sequence is a query, read when it is enumerated; any other's value is its body's, where its Spec.Requires hold
    /// (and they are proved at the call: the member throws where they do not). Lambdas passed to the member are
    /// inlined where they are pure; with others the member is a library call without a contract. The bodies run, so
    /// they are tested against the members they define.
    /// </summary>
    [AttributeUsage(AttributeTargets.Class)]
    public sealed class ComprehensionsAttribute : Attribute { }

    /// <summary>
    /// A model function: ghost state of an object whose class the program has no sources of, such as the elements
    /// of a <c>List&lt;T&gt;</c>. A static method whose first parameter is the object, and optionally a second one, a key
    /// (a dictionary's value at a key); it is a ghost field of the object, which stubs ([ContractsFor]) and
    /// specifications read, and calls of stubbed members change within their Spec.Modifies. Its Spec.Ensures hold of
    /// every value it has (a size is not negative; trusted); nothing else in its body is used (write
    /// <c>throw null!</c>). Calls to it are specification only, and are erased.
    /// </summary>
    [AttributeUsage(AttributeTargets.Method)]
    public sealed class ModelAttribute : Attribute { }
}
