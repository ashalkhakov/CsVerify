using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;

namespace CsVerify.Verifier.Boogie
{
    // Level 2: what Checks makes of the kernel (level 1, Kernel.cs). Expressions are mathematics (MLit, MVar, MOp,
    // MQuant, MFnApp; permission atoms over them inside Checks); statements are assignments, asserts and assumes,
    // calls and the state's changes, each obligation made. Heap rewrites the stores and allocations into map updates
    // and adds the loop frames (level 3, the same types); the printer reads level 3.

    /// <summary>
    /// One method at level 2 (and 3): what Checks makes of its contract and body. What method it is, how it is encoded,
    /// its effects and what it names are its kernel procedure's (<see cref="Source"/>).
    /// </summary>
    internal sealed class MProcedure
    {
        public KProcedure Source;
        public List<MSpec> Requires = new List<MSpec>(), Ensures = new List<MSpec>();
        public MExpr Frame, ReadsFrame, InferredReads, FunctionBody;
        /// <summary>The asserts at entry (the preconditions well-defined).</summary>
        public List<MStmt> Entry = new List<MStmt>();
        public List<MBlock> Blocks = new List<MBlock>();
        public int Obligations;
    }

    // ------------------------------------------------------------------ expressions

    internal abstract class MExpr { }

    /// <summary>A literal, as Boogie writes it ("5", "(-3)", "true", "null").</summary>
    internal sealed class MLit : MExpr
    {
        public string Text;
        public MLit(string text)
        {
            Text = text;
        }
    }

    /// <summary>A variable: a parameter, a local, a quantifier's variable, "result".</summary>
    internal sealed class MVar : MExpr
    {
        public string Name;
        public MVar(string name)
        {
            Name = name;
        }
    }

    /// <summary>
    /// An operation of Boogie's (or the prelude's): a binary or unary operator ("+", "&&", "!", "==>"...), "ite", "div"
    /// and "rem" (C#'s), "len", "old", "wrap" (an expression, the low end and the size), "sel" (a map, a reference, an
    /// index).
    /// </summary>
    internal sealed class MOp : MExpr
    {
        public string Op;
        public MExpr[] Args;
        public MOp(string op, params MExpr[] args)
        {
            Op = op;
            Args = args;
        }
    }

    /// <summary>forall or exists over an int variable: range ==> body, or range && body.</summary>
    internal sealed class MQuant : MExpr
    {
        public bool Forall;
        public string Var;
        /// <summary>Its variable's Boogie type (int, unless said).</summary>
        public string Type = "int";
        public MExpr Range, Body;
        /// <summary>Its triggers, each one on its own (null: the solver's choice).</summary>
        public MExpr[] Trigger;

        /// <summary>forall var: int, (range ==>) body.</summary>
        public static MQuant ForAll(string var, MExpr body, MExpr range = null) => ForAll(var, "int", body, range);

        /// <summary>forall var: type, (range ==>) body.</summary>
        public static MQuant ForAll(string var, string type, MExpr body, MExpr range = null) => Quant(true, var, type, body, range);

        /// <summary>exists var: int, (range &&) body.</summary>
        public static MQuant Exists(string var, MExpr body, MExpr range = null) => Exists(var, "int", body, range);

        /// <summary>exists var: type, (range &&) body.</summary>
        public static MQuant Exists(string var, string type, MExpr body, MExpr range = null) => Quant(false, var, type, body, range);

        private static MQuant Quant(bool forall, string var, string type, MExpr body, MExpr range) => new MQuant
        {
            Forall = forall,
            Var = var,
            Type = type,
            Range = range,
            Body = body,
        };
    }

    /// <summary>
    /// A function's value: the function, its layer (null: the caller's), the field maps it reads, its arguments (the
    /// receiver first, for an instance one); the element maps are the printer's.
    /// </summary>
    internal sealed class MFnApp : MExpr
    {
        public IMethodSymbol Callee;
        public string Function;
        public string Layer;
        public List<string> Fields = new List<string>();
        public MExpr[] Args;
        /// <summary>A function over a predicate: the snapshot of the instance its value is of (in place of the memory).</summary>
        public MExpr Snap;
        /// <summary>Of its arguments alone (a library stub's): no layer, no memory.</summary>
        public bool Plain;
        /// <summary>Of a snapshot of the memory (a call frame's, s<i>n</i>): its maps' names, so prefixed (null: the memory now).</summary>
        public string MapsAt;
    }

    /// <summary>Spec.Acc(Obj): (write) permission to an [Owned] object. A fact where permissions are given or got; else "in hand".</summary>
    internal sealed class MAcc : MExpr
    {
        public MExpr Obj;
        public ITypeSymbol Type;
        public SyntaxNode At;
    }

    /// <summary>Spec.Acc(Arr, Lo, Hi) (Spec.Acc(Arr): all its cells), or Spec.AccRead, a share to read: permission to the cells a[Lo..Hi).</summary>
    internal sealed class MCells : MExpr
    {
        public MExpr Arr, Lo, Hi;
        public bool Read;
        public SyntaxNode At;
    }

    /// <summary>Spec.Acc(Obj, nameof(C.F)): permission to one field of an [Owned] object (Viper's acc(o.f)).</summary>
    internal sealed class MFieldAcc : MExpr
    {
        public MExpr Obj;
        public ISymbol Field;
        public ITypeSymbol Type;
        public SyntaxNode At;
    }

    /// <summary>An instance of a [Predicate]: P(Args), its permissions folded into it.</summary>
    internal sealed class MInst : MExpr
    {
        public IMethodSymbol Pred;
        public MExpr[] Args;
        public SyntaxNode At;
    }

    /// <summary>Around a call that exchanges permissions, the caller keeps what it still holds (the program says which maps).</summary>
    internal sealed class MCallFrame : MStmt, IHeapStmt
    {
        public int Id;
        public bool After;
        public MExpr Receiver;
        public IMethodSymbol Callee;
        public List<string> Maps = new List<string>();
        /// <summary>A call that takes cells: those it was given (and the instances, whose folded cells go with them); it changes no others.</summary>
        public bool Cells;
        public List<(MExpr guard, MExpr atom)> Given = new List<(MExpr, MExpr)>();
        public List<string> ElementMaps = new List<string>();
        /// <summary>Each [Owned] map's field id (its single-field permission's).</summary>
        public Dictionary<string, int> FieldIds = new Dictionary<string, int>();
        public bool Fields;
        /// <summary>The globals the callee's postconditions read as they were (old): snapshotted before the call.</summary>
        public HashSet<string> OldGlobals = new HashSet<string>();
    }

    /// <summary>new E(...) of an exception type: a new exception of exactly that type (dtype).</summary>
    internal sealed class MNewExc : MStmt, IHeapStmt
    {
        public string Var;
        public ITypeSymbol Type;
    }

    /// <summary>
    /// The way a call (Call), or checked arithmetic (Overflow, out of range), throws instead: ex$ the
    /// exception, to the handlers at Target. The printer splits the block there.
    /// </summary>
    internal sealed class MFork : MStmt, IHeapStmt
    {
        public MCall Call;
        public MExpr Overflow;
        public string Target;
        /// <summary>The exception it throws, where it isn't a call's (null: any).</summary>
        public string Exception = "T#System.OverflowException";
    }

    /// <summary>A statement of level 2 (Checks'): those Heap rewrites (stores, allocations) are level 2's alone.</summary>
    internal abstract class MStmt { }

    /// <summary>
    /// A statement of level 3 (Heap's, what the printer reads): level 2's but the stores and allocations, and the loop
    /// frames Heap adds (HLoopFrame, HSnapshot, HConfinedFrame, HConfinedSnapshot), level 3's alone.
    /// </summary>
    internal interface IHeapStmt { }

    internal sealed class MAssign : MStmt, IHeapStmt
    {
        public string Var;
        public MExpr Value;
    }

    /// <summary>A write of a field, checked (a map's update, after Heap).</summary>
    internal sealed class MFieldStore : MStmt
    {
        public ISymbol Field;
        public MExpr Instance, Value;
        public bool OnThis;
        public SyntaxNode At, InstanceAt;
    }

    /// <summary>The tree roots change: Take's split (what was below the taken object is in its tree or the container's), Give's join.</summary>
    internal sealed class MRoots : MStmt, IHeapStmt
    {
        public bool Join;
        public MExpr Container, Child;
        public List<string> Siblings = new List<string>();
    }

    /// <summary>new C(args): an object allocated into Var, its fields their defaults, then its constructor (null: an implicit one).</summary>
    internal sealed class MNewObj : MStmt
    {
        public string Var;
        public ITypeSymbol Type;
        public IMethodSymbol Ctor;
        public MExpr[] Args;
        public SyntaxNode[] ArgsAt;
        public SyntaxNode At;
        public Check Check;
    }

    /// <summary>Map[Ref] := Value, Value a specification (a new array's row, a new list's Items or Size: LINQ's copies).</summary>
    internal sealed class MRow : MStmt
    {
        public string Map;
        public MExpr Ref, Value;
        /// <summary>Where the program writes the row (checked against Spec.Modifies, CSV1017); null for the kernel's own.</summary>
        public SyntaxNode At;
    }

    /// <summary>Memory cells [Lo, Hi) of Map's row at null set to Value (AllocArray's fill).</summary>
    internal sealed class MFill : MStmt
    {
        public string Map;
        public MExpr Lo, Hi, Value;
    }

    /// <summary>A write of an array's element, checked (a map's update, after Heap).</summary>
    internal sealed class MStore : MStmt
    {
        public MExpr Array, Index, Value;
        public ITypeSymbol ArrayType;
        public SyntaxNode At, ArrayAt;
    }

    /// <summary>new T[n] (with an initializer's elements): into Var.</summary>
    internal sealed class MNew : MStmt
    {
        public string Var;
        public ITypeSymbol ArrayType;
        public MExpr Size;
        public MExpr[] Elements;
    }

    internal sealed class MCall : MStmt, IHeapStmt
    {
        public IMethodSymbol Callee;
        /// <summary>The variables its ref and out arguments are (by parameter ordinal): they get what it gives back.</summary>
        public List<(int param, string var)> RefOuts = new List<(int, string)>();
        /// <summary>An instance method's receiver (null for a static one).</summary>
        public MExpr Receiver;
        public bool ReceiverIsThis;
        public SyntaxNode ReceiverAt;
        public MExpr[] Args;
        /// <summary>The variable its result goes to; null for none.</summary>
        public string Result;
        /// <summary>A struct's method that writes this: the variable the receiver's new value goes to.</summary>
        public string ThisOut;
        public SyntaxNode At;
        /// <summary>Where each argument is (for a non-null one's check).</summary>
        public SyntaxNode[] ArgsAt;
        public Check Check;
        /// <summary>Where an exception it throws goes, where exceptions are seen (a try's handlers, or the method's exit).</summary>
        public string ThrowsTo;
        /// <summary>2: a task's or thread's join, of the procedure's twin whose preconditions its start checked.</summary>
        public int Phase;
    }

    /// <summary>A call of a delegate (a Func or an Action): checked not null, and that it accepts the arguments.</summary>
    internal sealed class MInvoke : MStmt, IHeapStmt
    {
        public string Result;
        public MExpr Delegate;
        public MExpr[] Args;
        /// <summary>Its signature, as Boogie's types ("int.int"): which $pre, $post and $call.</summary>
        public string Key;
        public SyntaxNode At, DelegateAt;
    }

    /// <summary>
    /// A lambda made a delegate: a new reference, and what it accepts ($pre: its Spec.Requires, or anything) and gives
    /// ($post: its postconditions and an expression's value), for every argument; whether it changes nothing.
    /// </summary>
    internal sealed class MLambda : MStmt, IHeapStmt
    {
        public string Var, Key;
        public List<(string name, string type)> Params = new List<(string, string)>();
        public string ResultType;
        /// <summary>Its precondition (of the parameters q$x); null: it accepts anything.</summary>
        public MExpr Pre;
        /// <summary>What it gives (of the parameters, and "result").</summary>
        public List<MExpr> Posts = new List<MExpr>();
        public bool NoChange;
        /// <summary>The same in every state ($steady): its $pre and $post are those in every state.</summary>
        public bool Steady;
        /// <summary>One that reads state (its own Spec.Reads): its precondition in the state it's made in, and what it reads there.</summary>
        public MExpr PreS, Reads;
        /// <summary>A lambda of Spec.Reads that changes nothing: its postconditions, of the state it's made in (and of any that agrees with it on its frame).</summary>
        public List<MExpr> PostsS = new List<MExpr>();
        /// <summary>What it may change, for its arguments (its own Spec.Modifies).</summary>
        public MExpr Changes;
    }

    /// <summary>A call of code whose contract isn't known (IDisposable.Dispose, as using calls it): it may change anything.</summary>
    internal sealed class MHavocAll : MStmt, IHeapStmt
    {
        /// <summary>Unless this holds (a delegate's $nochange): then nothing changes.</summary>
        public MExpr Unless;
        /// <summary>The program's fields and arrays only: not the collections' models (code an Equals runs, not the collection's).</summary>
        public bool ProgramState;
    }

    /// <summary>Around a call of an async method: the objects of these (confined) locals, which no code can reach, are as they were.</summary>
    internal sealed class MKeep : MStmt, IHeapStmt
    {
        public int Id;
        public bool After;
        public List<string> Keep = new List<string>();
    }

    /// <summary>At a loop's head: every atomic field went by steps from where it was on entry (each change of it is one).</summary>
    internal sealed class MAtomicSteps : MStmt, IHeapStmt
    {
        /// <summary>The loop head whose entry took a snapshot of these maps (as{Head}map, as{Head}$Alloc), the steps since then; -1: since the method's entry.</summary>
        public int Head = -1;
        public List<string> Maps = new List<string>();
    }

    /// <summary>An await: other code may run, changing anything but the objects of these (confined) locals.</summary>
    internal sealed class MAwait : MStmt, IHeapStmt
    {
        public List<string> Keep = new List<string>();
        /// <summary>Only where this holds (a task it started still running); null: always.</summary>
        public MExpr When;
        /// <summary>The method holds permissions (cells, views): what they cover is kept too.</summary>
        public bool Cells, Perm;
    }

    internal sealed class MAssert : MStmt, IHeapStmt
    {
        public MExpr Cond;
        public Check Check;
        /// <summary>Holds unless this callee may write arrays (decided when the program is: what it calls is known then).</summary>
        public IMethodSymbol UnlessWritesArrays;
        /// <summary>What the callee must write for it to stand: "arrays" (the default), "fields" (fields but no arrays), "any".</summary>
        public string UnlessKind;
        /// <summary>Not assumed after it ({:subsumption 0}).</summary>
        public bool NotAssumedAfter;
    }

    internal sealed class MAssume : MStmt, IHeapStmt
    {
        public MExpr Cond;
        /// <summary>True in every state (what a field's type says of its value): not put under a guard or a quantifier.</summary>
        public bool Always;
    }

    internal sealed class MHavoc : MStmt, IHeapStmt
    {
        public string Var;
    }

    /// <summary>Level 3 (Heap's): map[Ref] := Value, or map[Ref][Index] := Value.</summary>
    internal sealed class MMapUpdate : MStmt, IHeapStmt
    {
        public string Map;
        public MExpr Ref, Index, Value;
    }

    internal sealed class MBlock
    {
        public string Label;
        /// <summary>The control-flow graph's block it is (or a branch of): which jumps are back edges.</summary>
        public int Ordinal;
        public List<MStmt> Stmts = new List<MStmt>();
        public KJump Jump;
    }

    // ------------------------------------------------------------------ level 3 (Heap's): what the printer reads

    /// <summary>
    /// One method at level 3: its level 2's (MProcedure) with its blocks and entry Heap's, the stores and allocations
    /// made map updates, the loop frames added.
    /// </summary>
    internal sealed class HProcedure
    {
        public KProcedure Source;
        public List<MSpec> Requires, Ensures;
        public MExpr Frame, ReadsFrame, InferredReads, FunctionBody;
        public List<IHeapStmt> Entry = new List<IHeapStmt>();
        public List<HBlock> Blocks = new List<HBlock>();
        public int Obligations;
        /// <summary>A copy (a twin's), of a copy of its kernel procedure.</summary>
        public HProcedure Clone()
        {
            var c = (HProcedure)MemberwiseClone();
            c.Source = Source.Clone();
            return c;
        }
    }

    internal sealed class HBlock
    {
        public string Label;
        /// <summary>The control-flow graph's block it is (or a branch of): which jumps are back edges.</summary>
        public int Ordinal;
        public List<IHeapStmt> Stmts = new List<IHeapStmt>();
        public KJump Jump;
    }

    /// <summary>
    /// At a loop head: the arrays the loop doesn't write (through a variable it doesn't change) are as they were when it
    /// was entered; the program says which maps (none where the loop calls what writes arrays).
    /// </summary>
    internal sealed class HLoopFrame : IHeapStmt
    {
        public int Head;
        public List<MExpr> Writers = new List<MExpr>();
        public HashSet<IMethodSymbol> Callees = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
        public List<string> Maps = new List<string>();
    }

    /// <summary>On the way into a loop: the maps its frame keeps, as they are now.</summary>
    internal sealed class HSnapshot : IHeapStmt
    {
        public HLoopFrame Frame;
    }

    /// <summary>
    /// At a loop head: the objects of confined locals the loop doesn't reassign (nobody else can reach them) are as they
    /// were on its entry, but for what the loop writes through those locals.
    /// </summary>
    internal sealed class HConfinedFrame : IHeapStmt
    {
        public int Head;
        /// <summary>Each local (its Boogie name), with the maps the loop writes through it ("$M." for any of a collection's models).</summary>
        public Dictionary<string, HashSet<string>> Locals = new Dictionary<string, HashSet<string>>();
    }

    /// <summary>On the way into a loop: every state map, as it is now (for its HConfinedFrame).</summary>
    internal sealed class HConfinedSnapshot : IHeapStmt
    {
        public int Head;
    }

    internal sealed class MSpec
    {
        public MExpr Expr;
        public SyntaxNode At;
        /// <summary>For a requires: what a failure of it at a call is about.</summary>
        public Check Check;
    }
}
