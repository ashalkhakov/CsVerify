using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;

namespace CsVerify.Verifier.Boogie
{
    // The passes from Roslyn to Boogie, each from one level's trees to the next's (docs/boogie.md):
    //   level 0    Roslyn's operations and control-flow graph
    //   Lowering:  level 0 -> level 1, the kernel ("idealized C#", this file): blocks of kernel statements, C#'s meaning
    //              kept in typed nodes (KArith, KConv, KElem, KLen, KFnCall), checks not yet made
    //   Checks:    level 1 -> level 2 (Math.cs): each of those nodes made mathematics, and the asserts (and assumes) it
    //              needs, in evaluation order; well-definedness, postconditions at returns, invariants and measures,
    //              termination, non-null arguments
    //   Heap:      level 2 -> level 3 (the same types): stores and allocations made map updates; what each procedure modifies
    //   Printer:   level 3 -> Boogie text, and which line is which check

    /// <summary>How integer arithmetic is meant where it is.</summary>
    internal enum KMode
    {
        /// <summary>C#'s default context: overflow is an obligation.</summary>
        Default,
        /// <summary>checked: overflow throws, which ends the path.</summary>
        Checked,
        /// <summary>unchecked: wraps around.</summary>
        Unchecked,
        /// <summary>specifications and ghost code: mathematics.</summary>
        Math,
    }

    // ------------------------------------------------------------------ expressions

    internal abstract partial class KExpr { }

    /// <summary>A literal, as Boogie writes it ("5", "(-3)", "true", "null").</summary>
    internal sealed class KLit : KExpr
    {
        public string Text;
        public KLit(string text)
        {
            Text = text;
        }

        public static KLit True => new KLit("true");
        public static KLit False => new KLit("false");
        public static KLit Null => new KLit("null");
        public static KLit Zero => new KLit("0");
        public static KLit One => new KLit("1");
        public static KLit MinusOne => new KLit("(-1)");
    }

    /// <summary>A variable: a parameter, a local, a quantifier's variable, "result".</summary>
    internal sealed class KVar : KExpr
    {
        public string Name;
        public KVar(string name)
        {
            Name = name;
        }
    }

    /// <summary>
    /// An operation of Boogie's (or the prelude's): a binary or unary operator ("+", "&&", "!", "==>"...), "ite", "div"
    /// and "rem" (C#'s), "len", "old", "wrap" (an expression, the low end and the size), "sel" (a map, a reference, an
    /// index).
    /// </summary>
    internal sealed class KOp : KExpr
    {
        public string Op;
        public KExpr[] Args;
        public KOp(string op, params KExpr[] args)
        {
            Op = op;
            Args = args;
        }

        /// <summary>A map read: map[at] (map[at][at2], with two).</summary>
        public static KOp Sel(string map, params KExpr[] at) => new KOp("sel", at.Prepend(new KVar(map)).ToArray());

        /// <summary>A map with one entry changed: map[at := value].</summary>
        public static KOp Store(string map, KExpr at, KExpr value) => new KOp("store", new KVar(map), at, value);

        public static KOp Eq(KExpr a, KExpr b) => new KOp("==", a, b);
        public static KOp Ne(KExpr a, KExpr b) => new KOp("!=", a, b);
        public static KOp Not(KExpr a) => new KOp("!", a);
        public static KOp AndAlso(KExpr a, KExpr b) => new KOp("&&", a, b);
        public static KOp OrElse(KExpr a, KExpr b) => new KOp("||", a, b);
        public static KOp Lt(KExpr a, KExpr b) => new KOp("<", a, b);
        public static KOp Le(KExpr a, KExpr b) => new KOp("<=", a, b);
        public static KOp Gt(KExpr a, KExpr b) => new KOp(">", a, b);
        public static KOp Ge(KExpr a, KExpr b) => new KOp(">=", a, b);
        public static KOp Plus(KExpr a, KExpr b) => new KOp("+", a, b);
        public static KOp Minus(KExpr a, KExpr b) => new KOp("-", a, b);
        public static KOp Implies(KExpr a, KExpr b) => new KOp("==>", a, b);
        public static KOp Ite(KExpr c, KExpr then, KExpr otherwise) => new KOp("ite", c, then, otherwise);

        /// <summary>A read of a map given as an expression: map[at] (map[at][at2], with two).</summary>
        public static KOp Sel(KExpr map, params KExpr[] at) => new KOp("sel", at.Prepend(map).ToArray());

        /// <summary>A map given as an expression, with one entry changed: map[at := value].</summary>
        public static KOp Store(KExpr map, KExpr at, KExpr value) => new KOp("store", map, at, value);

        public static KOp Times(KExpr a, KExpr b) => new KOp("*", a, b);
        public static KOp Length(KExpr a) => new KOp("len", a);
        public static KOp Old(KExpr a) => new KOp("old", a);

        /// <summary>A map as Boogie's lambda: (lambda binder :: body), the binder written out ("o$: Ref").</summary>
        public static KOp MapLambda(string binder, KExpr body) => new KOp("lambda", new KLit(binder), body);

        public static KOp IsNull(KExpr a) => new KOp("==", a, KLit.Null);
        public static KOp NotNull(KExpr a) => new KOp("!=", a, KLit.Null);
    }

    /// <summary>forall or exists over an int variable: range ==> body, or range && body.</summary>
    internal sealed class KQuant : KExpr
    {
        public bool Forall;
        public string Var;
        /// <summary>Its variable's Boogie type (int, unless said).</summary>
        public string Type = "int";
        public KExpr Range, Body;
        /// <summary>Its triggers, each one on its own (null: the solver's choice).</summary>
        public KExpr[] Trigger;

        /// <summary>forall var: int, (range ==>) body.</summary>
        public static KQuant ForAll(string var, KExpr body, KExpr range = null) => ForAll(var, "int", body, range);

        /// <summary>forall var: type, (range ==>) body.</summary>
        public static KQuant ForAll(string var, string type, KExpr body, KExpr range = null) => Quant(true, var, type, body, range);

        /// <summary>exists var: int, (range &&) body.</summary>
        public static KQuant Exists(string var, KExpr body, KExpr range = null) => Exists(var, "int", body, range);

        /// <summary>exists var: type, (range &&) body.</summary>
        public static KQuant Exists(string var, string type, KExpr body, KExpr range = null) => Quant(false, var, type, body, range);

        private static KQuant Quant(bool forall, string var, string type, KExpr body, KExpr range) => new KQuant
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
    internal sealed class KFnApp : KExpr
    {
        public IMethodSymbol Callee;
        public string Function;
        public string Layer;
        public List<string> Fields = new List<string>();
        public KExpr[] Args;
        /// <summary>A function over a predicate: the snapshot of the instance its value is of (in place of the memory).</summary>
        public KExpr Snap;
        /// <summary>Of its arguments alone (a library stub's): no layer, no memory.</summary>
        public bool Plain;
        /// <summary>Of a snapshot of the memory (a call frame's, s<i>n</i>): its maps' names, so prefixed (null: the memory now).</summary>
        public string MapsAt;
    }

    // (C#'s meaning, until Checks)

    /// <summary>+ - * / % of C# integers, in a mode.</summary>
    internal sealed class KArith : KExpr
    {
        public string Op;
        public KExpr Left, Right;
        public ITypeSymbol Type;
        public KMode Mode;
        public SyntaxNode At;
        /// <summary>Where an OverflowException it throws (checked, or MinValue / -1) goes, where exceptions are seen.</summary>
        public string ThrowsTo;
    }

    /// <summary>An explicit conversion between integer types.</summary>
    internal sealed class KConv : KExpr
    {
        public KExpr Value;
        public ITypeSymbol From, To;
        public KMode Mode;
        public SyntaxNode At;
    }

    /// <summary>
    /// A collection read through its interface (IList, IReadOnlyList, ICollection, IReadOnlyCollection): its Count, or
    /// its element at Index. An array's, a modeled collection's, or else a value of the state (Fresh: unknown at each read).
    /// </summary>
    internal sealed class KIfc : KExpr
    {
        public bool Item;
        public KExpr Of, Index;
        public ITypeSymbol Element;
        public bool Fresh;
        public SyntaxNode At, OfAt;
    }

    /// <summary>let Var = Value in Body: a local of a [Pure] body of statements (Checks substitutes it).</summary>
    internal sealed class KLet : KExpr
    {
        public string Var;
        public KExpr Value, Body;

        public static KLet Of(string var, KExpr value, KExpr body) => new KLet
        {
            Var = var,
            Value = value,
            Body = body,
        };
    }

    /// <summary>Spec.Multiset(a, n): the multiset of an integer array's a[0..n), unfolded Levels elements where it's used.</summary>
    internal sealed class KMultiset : KExpr
    {
        public KExpr Array, Count;
        public ITypeSymbol ArrayType;
        public int Levels;
        public SyntaxNode At;
    }

    /// <summary>An array's element (a read): checked for null and bounds in code, well-defined if so in a specification.</summary>
    internal sealed class KElem : KExpr
    {
        /// <summary>A string's character (s[i]), not an array's element.</summary>
        public bool String;
        /// <summary>A collection's element in a specification: of this model (Items, Entries), where the index is below Size or in this Domain.</summary>
        public string Model, Domain;
        public KExpr Array, Index;
        public ITypeSymbol ArrayType;
        public bool InSpec;
        /// <summary>A rectangular array's cell ($cell of its indices): each index checked against its dimension already, not against the length.</summary>
        public bool Unchecked;
        /// <summary>A span's cell: of its base, which a span within bounds has (no null check).</summary>
        public bool NoNull;
        /// <summary>In code that may run alongside other code (true, or while its tasks run): under cell permissions, its cell must be held to read (CSV1016).</summary>
        public KExpr Alongside;
        public SyntaxNode At, ArrayAt;
    }

    /// <summary>An array's length (or a string's, where String says so).</summary>
    internal sealed class KLen : KExpr
    {
        public bool String;
        public KExpr Array;
        public bool InSpec;
        public SyntaxNode At, ArrayAt;
    }

    /// <summary>A function's call in a specification: well-defined where its receiver isn't null and its precondition holds at the arguments.</summary>
    internal sealed class KFnCall : KExpr
    {
        public IMethodSymbol Callee;
        /// <summary>An instance one's receiver (null for a static one).</summary>
        public KExpr Receiver;
        public bool ReceiverIsThis;
        public KExpr[] Args;
        public SyntaxNode At, ReceiverAt;
        /// <summary>A [Pure] library member with a stub contract (a string's): a function its contract says all of, in code too.</summary>
        public bool Stub;
    }

    /// <summary>A field's value: of an object (checked not null, unless it is this), or a static field's (of the one object, null).</summary>
    internal sealed class KField : KExpr
    {
        public ISymbol Field;
        /// <summary>The object; null for a static field.</summary>
        public KExpr Instance;
        public bool OnThis;
        /// <summary>Of an object known not null where it's read (a property pattern's, after its null test): not checked.</summary>
        public bool NoNull;
        public SyntaxNode At, InstanceAt;
    }

    /// <summary>Spec.Acc(Obj): (write) permission to an [Owned] object. A fact where permissions are given or got; else "in hand".</summary>
    internal sealed class KAcc : KExpr
    {
        public KExpr Obj;
        public ITypeSymbol Type;
        public SyntaxNode At;
    }

    /// <summary>Spec.Acc(Arr, Lo, Hi) (Spec.Acc(Arr): all its cells), or Spec.AccRead, a share to read: permission to the cells a[Lo..Hi).</summary>
    internal sealed class KCells : KExpr
    {
        public KExpr Arr, Lo, Hi;
        public bool Read;
        public SyntaxNode At;
    }

    /// <summary>Spec.Acc(Obj, nameof(C.F)): permission to one field of an [Owned] object (Viper's acc(o.f)).</summary>
    internal sealed class KFieldAcc : KExpr
    {
        public KExpr Obj;
        public ISymbol Field;
        public ITypeSymbol Type;
        public SyntaxNode At;
    }

    /// <summary>An instance of a [Predicate]: P(Args), its permissions folded into it.</summary>
    internal sealed class KInst : KExpr
    {
        public IMethodSymbol Pred;
        public KExpr[] Args;
        public SyntaxNode At;
    }

    // ------------------------------------------------------------------ statements

    /// <summary>Spec.Fold(Inst) or Spec.Unfold(Inst).</summary>
    internal sealed class KFold : KStmt
    {
        public KInst Inst;
        public bool Unfold;
        public SyntaxNode At, InstAt;
    }

    /// <summary>After Checks: around a call that exchanges permissions, the caller keeps what it still holds (the program says which maps).</summary>
    internal sealed class KCallFrame : KStmt
    {
        public int Id;
        public bool After;
        public KExpr Receiver;
        public IMethodSymbol Callee;
        public List<string> Maps = new List<string>();
        /// <summary>A call that takes cells: those it was given (and the instances, whose folded cells go with them); it changes no others.</summary>
        public bool Cells;
        public List<(KExpr guard, KExpr atom)> Given = new List<(KExpr, KExpr)>();
        public List<string> ElementMaps = new List<string>();
        /// <summary>Each [Owned] map's field id (its single-field permission's).</summary>
        public Dictionary<string, int> FieldIds = new Dictionary<string, int>();
        public bool Fields;
        /// <summary>The globals the callee's postconditions read as they were (old): snapshotted before the call.</summary>
        public HashSet<string> OldGlobals = new HashSet<string>();
    }

    /// <summary>throw Value: not null (CSV1013, but in a proof); where exceptions are seen, it is the exception (ex$).</summary>
    internal sealed class KThrow : KStmt
    {
        public KExpr Value;
        public bool Seen;
        public SyntaxNode At;
    }

    /// <summary>new E(...) of an exception type: a new exception of exactly that type (dtype).</summary>
    internal sealed class KNewExc : KStmt
    {
        public string Var;
        public ITypeSymbol Type;
    }

    /// <summary>Leaving the method by an exception (ex$): its own EnsuresOnThrow clauses for the exception's type hold (CSV1002).</summary>
    internal sealed class KThrowExit : KStmt { }

    /// <summary>
    /// After Checks: the way a call (Call), or checked arithmetic (Overflow, out of range), throws instead: ex$ the
    /// exception, to the handlers at Target. The printer splits the block there.
    /// </summary>
    internal sealed class KFork : KStmt
    {
        public KCall Call;
        public KExpr Overflow;
        public string Target;
        /// <summary>The exception it throws, where it isn't a call's (null: any).</summary>
        public string Exception = "T#System.OverflowException";
    }

    internal abstract class KStmt { }

    internal sealed class KAssign : KStmt
    {
        public string Var;
        public KExpr Value;
        /// <summary>A local of non-nullable type: where its write is checked not null (CSV1014), and its name.</summary>
        public SyntaxNode NotNullAt;
        public string NotNullName;

        public static KAssign Of(string var, KExpr value, SyntaxNode notNullAt = null, string notNullName = null) => new KAssign
        {
            Var = var,
            Value = value,
            NotNullAt = notNullAt,
            NotNullName = notNullName,
        };
    }

    /// <summary>A write of a field (checked, until Checks; a map's, after Heap).</summary>
    internal sealed class KFieldStore : KStmt
    {
        public ISymbol Field;
        public KExpr Instance, Value;
        public bool OnThis;
        public SyntaxNode At, InstanceAt;
    }

    /// <summary>Own.New(obj, out View) (Kind "new": the view of a new object) or Own.Drop(Obj) (Kind "drop").</summary>
    internal sealed class KOwn : KStmt
    {
        public string Kind;
        public KExpr Obj;
        public string View;
        public ITypeSymbol Type;
        public SyntaxNode At;
        /// <summary>Own.New of an object not made there: reported already (CSV1016), its invariant not proved again.</summary>
        public bool Unchecked;
        /// <summary>Own.Take and Own.Give: the [Owns] field, the object given and its view, as written.</summary>
        public ISymbol Field;
        public KExpr Value, ViewValue;
        public SyntaxNode SlotAt, ValueAt, ViewAt;
        /// <summary>A view packed: the package's type.</summary>
        public ITypeSymbol Into;
    }

    /// <summary>The tree roots change: Take's split (what was below the taken object is in its tree or the container's), Give's join.</summary>
    internal sealed class KRoots : KStmt
    {
        public bool Join;
        public KExpr Container, Child;
        public List<string> Siblings = new List<string>();
    }

    /// <summary>new C(args): an object allocated into Var, its fields their defaults, then its constructor (null: an implicit one).</summary>
    internal sealed class KNewObj : KStmt
    {
        public string Var;
        public ITypeSymbol Type;
        public IMethodSymbol Ctor;
        public KExpr[] Args;
        public SyntaxNode[] ArgsAt;
        public SyntaxNode At;
        public Check Check;
    }

    /// <summary>A view's cells come into hand (Grant), or go (they're another's now, or freed).</summary>
    internal sealed class KMemCells : KStmt
    {
        public List<KCells> Cells;
        public bool Grant;

        public static KMemCells Of(List<KCells> cells, bool grant) => new KMemCells
        {
            Cells = cells,
            Grant = grant,
        };
    }

    /// <summary>
    /// The arrays a library call may read or write (Checks, which knows whether the method holds cell permissions): without
    /// them, where it may write, every element map unknown (Fresh, a map each); with them, all the cells of each array
    /// it's handed held (to write, wholly; to read, some), and those it may write unknown (Rows, a row each), where it's
    /// handed nothing else (Plain).
    /// </summary>
    internal sealed class KLibraryArrays : KStmt
    {
        public List<(KExpr array, string map, string row)> Arrays = new List<(KExpr, string, string)>();
        public List<(string map, string fresh)> Fresh = new List<(string, string)>();
        public bool Write, Plain;
        public SyntaxNode At;
    }

    /// <summary>Map[Ref] := Value, Value a specification (a new array's row, a new list's Items or Size: LINQ's copies).</summary>
    internal sealed class KRow : KStmt
    {
        public string Map;
        public KExpr Ref, Value;
        /// <summary>Where the program writes the row (checked against Spec.Modifies, CSV1017); null for the kernel's own.</summary>
        public SyntaxNode At;

        public static KRow Of(string map, KExpr @ref, KExpr value, SyntaxNode at = null) => new KRow
        {
            Map = map,
            Ref = @ref,
            Value = value,
            At = at,
        };
    }

    /// <summary>Memory cells [Lo, Hi) of Map's row at null set to Value (AllocArray's fill).</summary>
    internal sealed class KFill : KStmt
    {
        public string Map;
        public KExpr Lo, Hi, Value;
    }

    /// <summary>A write of an array's element (checked for null and bounds, until Checks; a map's, after).</summary>
    internal sealed class KStore : KStmt
    {
        /// <summary>A memory cell (the row at null), written through a view: no array to check.</summary>
        public bool Memory;
        public KExpr Array, Index, Value;
        public ITypeSymbol ArrayType;
        public SyntaxNode At, ArrayAt;
        /// <summary>A rectangular array's cell: each index checked against its dimension already, not against the length.</summary>
        public bool Unchecked;
        /// <summary>A span's cell: of its base, which a span within bounds has (no null check).</summary>
        public bool NoNull;
        /// <summary>After Checks: checked.</summary>
        public bool Checked;
    }

    /// <summary>new T[n] (with an initializer's elements): into Var.</summary>
    internal sealed class KNew : KStmt
    {
        public string Var;
        public ITypeSymbol ArrayType;
        public KExpr Size;
        public KExpr[] Elements;

        public static KNew Of(string var, ITypeSymbol arrayType, KExpr size, KExpr[] elements = null) => new KNew
        {
            Var = var,
            ArrayType = arrayType,
            Size = size,
            Elements = elements,
        };
    }

    internal sealed class KCall : KStmt
    {
        public IMethodSymbol Callee;
        /// <summary>The variables its ref and out arguments are (by parameter ordinal): they get what it gives back.</summary>
        public List<(int param, string var)> RefOuts = new List<(int, string)>();
        /// <summary>An instance method's receiver (null for a static one).</summary>
        public KExpr Receiver;
        public bool ReceiverIsThis;
        public SyntaxNode ReceiverAt;
        public KExpr[] Args;
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
        /// <summary>
        /// A call that runs alongside (a task's, a thread's): 1, its start, where its preconditions are checked and the
        /// permissions they ask for given; 2, its join (of <see cref="Started"/>), where it returns what its postconditions give.
        /// </summary>
        public int Phase;
        public KCall Started;
    }

    /// <summary>A call of a delegate (a Func or an Action): checked not null, and that it accepts the arguments.</summary>
    internal sealed class KInvoke : KStmt
    {
        public string Result;
        public KExpr Delegate;
        public KExpr[] Args;
        /// <summary>Its signature, as Boogie's types ("int.int"): which $pre, $post and $call.</summary>
        public string Key;
        public SyntaxNode At, DelegateAt;
    }

    /// <summary>
    /// A lambda made a delegate: a new reference, and what it accepts ($pre: its Spec.Requires, or anything) and gives
    /// ($post: its postconditions and an expression's value), for every argument; whether it changes nothing.
    /// </summary>
    internal sealed class KLambda : KStmt
    {
        public string Var, Key;
        public List<(string name, string type)> Params = new List<(string, string)>();
        public string ResultType;
        /// <summary>Its precondition (of the parameters q$x); null: it accepts anything.</summary>
        public KExpr Pre;
        /// <summary>What it gives (of the parameters, and "result").</summary>
        public List<KExpr> Posts = new List<KExpr>();
        public bool NoChange;
        /// <summary>The same in every state ($steady): its $pre and $post are those in every state.</summary>
        public bool Steady;
        /// <summary>One that reads state (its own Spec.Reads): its precondition in the state it's made in, and what it reads there.</summary>
        public KExpr PreS, Reads;
        /// <summary>A lambda of Spec.Reads that changes nothing: its postconditions, of the state it's made in (and of any that agrees with it on its frame).</summary>
        public List<KExpr> PostsS = new List<KExpr>();
        /// <summary>What it may change, for its arguments (its own Spec.Modifies).</summary>
        public KExpr Changes;
        /// <summary>A method group's parameters, as its contract names them, to the bound variables.</summary>
        public Dictionary<string, KExpr> Rename = new Dictionary<string, KExpr>();
    }

    /// <summary>A check Lowering decides on: a specification (mathematics, its own well-definedness not checked), reported as given.</summary>
    internal sealed class KCheck : KStmt
    {
        public KExpr Cond;
        public string Id, Message;
        public SyntaxNode At;
        /// <summary>Not assumed after it: a report, not a fact.</summary>
        public bool NotAssumedAfter;

        public static KCheck Of(KExpr cond, string id, SyntaxNode at, string message, bool notAssumedAfter = false) => new KCheck
        {
            Cond = cond,
            Id = id,
            At = at,
            Message = message,
            NotAssumedAfter = notAssumedAfter,
        };
    }

    /// <summary>A call of code whose contract isn't known (IDisposable.Dispose, as using calls it): it may change anything.</summary>
    internal sealed class KHavocAll : KStmt
    {
        /// <summary>Unless this holds (a delegate's $nochange): then nothing changes.</summary>
        public KExpr Unless;
        /// <summary>The program's fields and arrays only: not the collections' models (code an Equals runs, not the collection's).</summary>
        public bool ProgramState;
    }

    /// <summary>Around a call of an async method: the objects of these (confined) locals, which no code can reach, are as they were.</summary>
    internal sealed class KKeep : KStmt
    {
        public int Id;
        public bool After;
        public List<string> Keep = new List<string>();
    }

    /// <summary>At a loop's head: every atomic field went by steps from where it was on entry (each change of it is one).</summary>
    internal sealed class KAtomicSteps : KStmt
    {
        /// <summary>The loop head whose entry took a snapshot of these maps (as{Head}map, as{Head}$Alloc), the steps since then; -1: since the method's entry.</summary>
        public int Head = -1;
        public List<string> Maps = new List<string>();
    }

    /// <summary>An await: other code may run, changing anything but the objects of these (confined) locals.</summary>
    internal sealed class KAwait : KStmt
    {
        public List<string> Keep = new List<string>();
        /// <summary>Only where this holds (a task it started still running); null: always.</summary>
        public KExpr When;
        /// <summary>The method holds permissions (cells, views): what they cover is kept too.</summary>
        public bool Cells, Perm;
    }

    /// <summary>A data value's field: checked not null in code, well-defined if so in a specification.</summary>
    internal sealed class KDataField : KExpr
    {
        public string Function;
        public KExpr Value;
        public SyntaxNode At, ValueAt;
        /// <summary>A struct's field: the value is never null.</summary>
        public bool Struct;
    }

    /// <summary>A cast to a data type: checked (an InvalidCastException in code, ill-defined in a specification).</summary>
    internal sealed class KCast : KExpr
    {
        public KExpr Value, Test;
        public SyntaxNode At;
    }

    internal sealed class KAssert : KStmt
    {
        public KExpr Cond;
        public Check Check;
        /// <summary>Holds unless this callee may write arrays (decided when the program is: what it calls is known then).</summary>
        public IMethodSymbol UnlessWritesArrays;
        /// <summary>What the callee must write for it to stand: "arrays" (the default), "fields" (fields but no arrays), "any".</summary>
        public string UnlessKind;
        /// <summary>Not assumed after it ({:subsumption 0}).</summary>
        public bool NotAssumedAfter;
    }

    internal sealed class KAssume : KStmt
    {
        public KExpr Cond;
        /// <summary>True in every state (what a field's type says of its value): not put under a guard or a quantifier.</summary>
        public bool Always;

        public static KAssume Of(KExpr cond, bool always = false) => new KAssume
        {
            Cond = cond,
            Always = always,
        };
    }

    /// <summary>An immutable object of a class with invariants, where a condition holds: its invariants hold (Checks' ObjectInvariant).</summary>
    internal sealed class KAssumeInvariant : KStmt
    {
        public KExpr Obj, When;
        public ITypeSymbol Type;

        public static KAssumeInvariant Of(KExpr obj, KExpr when, ITypeSymbol type) => new KAssumeInvariant
        {
            Obj = obj,
            When = when,
            Type = type,
        };
    }

    internal sealed class KHavoc : KStmt
    {
        public string Var;

        public static KHavoc Of(string var) => new KHavoc { Var = var };
    }

    /// <summary>Spec.Assert or Spec.Assume, until Checks: well-defined, then asserted (or assumed).</summary>
    internal sealed class KSpecStmt : KStmt
    {
        public KExpr Spec;
        public bool Assume;
        /// <summary>A fact assumed as it is (what a library member gives, as mathematics): no well-definedness of its own.</summary>
        public bool Free;
        public SyntaxNode At, ArgumentAt;

        public static KSpecStmt Assumed(KExpr spec, SyntaxNode at, SyntaxNode argumentAt = null) => new KSpecStmt
        {
            Spec = spec,
            At = at,
            ArgumentAt = argumentAt,
            Assume = true,
        };

        public static KSpecStmt AssumedFree(KExpr spec, SyntaxNode at, SyntaxNode argumentAt = null) => new KSpecStmt
        {
            Spec = spec,
            At = at,
            ArgumentAt = argumentAt,
            Assume = true,
            Free = true,
        };
    }

    /// <summary>After Heap: map[Ref] := Value, or map[Ref][Index] := Value.</summary>
    internal sealed class KMapUpdate : KStmt
    {
        public string Map;
        public KExpr Ref, Index, Value;
    }

    // ------------------------------------------------------------------ blocks and procedures

    internal abstract class KJump { }

    /// <summary>To one of these blocks (a choice, where there are several).</summary>
    internal sealed class KGoto : KJump
    {
        public List<string> Targets;
        public KGoto(params string[] targets)
        {
            Targets = targets.ToList();
        }
    }

    /// <summary>A return, from here (where its postconditions are reported).</summary>
    internal sealed class KReturn : KJump
    {
        public SyntaxNode At;

        public static KReturn Of(SyntaxNode at) => new KReturn { At = at };
    }

    /// <summary>The path ends (a throw, or what can't be reached).</summary>
    internal sealed class KStop : KJump { }

    internal sealed class KBlock
    {
        public string Label;
        /// <summary>The control-flow graph's block it is (or a branch of): which jumps are back edges.</summary>
        public int Ordinal;
        public List<KStmt> Stmts = new List<KStmt>();
        public KJump Jump;

        public static KBlock Of(string label, int ordinal, KJump jump = null) => new KBlock
        {
            Label = label,
            Ordinal = ordinal,
            Jump = jump,
        };
    }

    internal sealed class KLocal
    {
        public string Name;
        public ITypeSymbol Type;
        /// <summary>A Boogie type of its own (a snapshot of a map), in place of Type's.</summary>
        public string Raw;

        public static KLocal Of(string name, string raw, ITypeSymbol type = null) => new KLocal
        {
            Name = name,
            Raw = raw,
            Type = type,
        };
    }

    /// <summary>
    /// After Heap, at a loop head: the arrays the loop doesn't write (through a variable it doesn't change) are as
    /// they were when it was entered; the program says which maps (none where the loop calls what writes arrays).
    /// </summary>
    internal sealed class KLoopFrame : KStmt
    {
        public int Head;
        public List<KExpr> Writers = new List<KExpr>();
        public HashSet<IMethodSymbol> Callees = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
        public List<string> Maps = new List<string>();
    }

    /// <summary>On the way into a loop: the maps its frame keeps, as they are now.</summary>
    internal sealed class KSnapshot : KStmt
    {
        public KLoopFrame Frame;
    }

    /// <summary>
    /// At a loop head: the objects of confined locals the loop doesn't reassign (nobody else can reach them) are as they
    /// were on its entry, but for what the loop writes through those locals.
    /// </summary>
    internal sealed class KConfinedFrame : KStmt
    {
        public int Head;
        /// <summary>Each local (its Boogie name), with the maps the loop writes through it ("$M." for any of a collection's models).</summary>
        public Dictionary<string, HashSet<string>> Locals = new Dictionary<string, HashSet<string>>();
    }

    /// <summary>On the way into a loop: every state map, as it is now (for its KConfinedFrame).</summary>
    internal sealed class KConfinedSnapshot : KStmt
    {
        public int Head;
    }

    internal sealed class KSpec
    {
        public KExpr Expr;
        public SyntaxNode At;

        public static KSpec Of(KExpr expr, SyntaxNode at) => new KSpec
        {
            Expr = expr,
            At = at,
        };
    }

    /// <summary>
    /// One method at level 1, as Lowering makes it; Checks makes level 2's of it (MProcedure, Math.cs), which keeps this
    /// one for what doesn't change: what method it is, how it is encoded, its effects and what it names. The fields are
    /// grouped by what they are, each group saying who sets it.
    /// </summary>
    internal sealed class KProcedure
    {
        public KProcedure Clone() => (KProcedure)MemberwiseClone();

        // ---- what method it is: set by Lowering's constructor

        public IMethodSymbol Method;
        public Contract Contract;
        public MethodResult Result;
        public string Name;
        public List<IParameterSymbol> Params;
        /// <summary>Ghost code ([GhostFunction], a lemma): its arithmetic is mathematics.</summary>
        public bool Ghost;
        /// <summary>An instance method or constructor: its receiver is the parameter this.</summary>
        public bool HasThis;
        public bool IsCtor;
        /// <summary>A list's constructor, from its stub: a procedure that returns the new list.</summary>
        public bool ListCtor;
        /// <summary>A struct's constructor: it gives the value it makes (this, a value it writes, its default to begin with).</summary>
        public bool StructThis;
        /// <summary>A struct's method that writes this: this by reference, in as this$in, out as this (as a ref parameter).</summary>
        public bool StructRefThis;
        /// <summary>A method of an [Owned] class that isn't [Pure] (or its constructor): it holds this object's view.</summary>
        public bool ThisIsView;
        /// <summary>A [Predicate]: its body (FunctionBody, its arithmetic as code's) is checked self-framing, once.</summary>
        public bool IsPredicate;
        /// <summary>An abstract member: a procedure with no body, which calls go to.</summary>
        public bool Abstract;
        /// <summary>A method whose body doesn't translate: its contract alone, for its callers (it may write what the effects analysis says).</summary>
        public bool Opaque;
        /// <summary>A twin's (BoogieTranslator): its preconditions free (a join's call, checked at its start).</summary>
        public bool FreeRequires;

        // ---- how it is encoded: UsesPerm and MemViews by Lowering.Modes before lowering; the rest by Checks.DecideCellModes

        /// <summary>It holds, gives or checks views: its permissions (perm, object to whether its view is in hand) are kept.</summary>
        public bool UsesPerm;
        /// <summary>It holds memory views (ATS's): cells in hand as views say (array mode).</summary>
        public bool MemViews;
        /// <summary>It keeps cell permissions (cells, cowner): it exchanges some, or names them.</summary>
        public bool UsesCells;
        /// <summary>Its contract names cells: it holds none but those it is given (else every cell, but those it gives away).</summary>
        public bool ArrayMode;
        /// <summary>It keeps single-field permissions (fperm, fowner): the program uses some.</summary>
        public bool UsesFields;

        // ---- its contract, as kernel expressions: by Lowering (Checks makes level 2's of them)

        public List<KSpec> Requires = new List<KSpec>(), Ensures = new List<KSpec>();
        /// <summary>Spec.Decreases of the method: its parameters' measure.</summary>
        public List<KExpr> Decreases;
        /// <summary>Spec.EnsuresOnThrow&lt;E&gt;(Cond): what holds where it leaves by throwing an E.</summary>
        public List<(ITypeSymbol type, KExpr cond, SyntaxNode at)> ThrowEnsures = new List<(ITypeSymbol, KExpr, SyntaxNode)>();
        /// <summary>Its Spec.Modifies: the objects (an ObjSet, a [Ref]bool) whose fields and cells it may write, as of entry.</summary>
        public KExpr Frame;
        /// <summary>A function's Spec.Reads: the objects whose fields and cells its value depends on (a frame axiom says so).</summary>
        public KExpr ReadsFrame;
        /// <summary>A [Pure] or [GhostFunction] method of one expression: a function too, of this body.</summary>
        public KExpr FunctionBody;
        /// <summary>An override that states its own precondition: it, and each base's, which must imply it (CSV1018).</summary>
        public List<KExpr> OwnRequires = new List<KExpr>();
        public List<(IMethodSymbol method, List<KExpr> requires)> BaseRequires = new List<(IMethodSymbol, List<KExpr>)>();
        /// <summary>A base's Spec.Modifies, which its own must lie within (CSV1018).</summary>
        public List<(IMethodSymbol method, KExpr frame)> BaseFrames = new List<(IMethodSymbol, KExpr)>();
        /// <summary>The roots of the trees it borrows through Spec.Modifies(Own.Tree(x)), over its parameters as on entry.</summary>
        public readonly List<KExpr> LentRoots = new List<KExpr>();
        /// <summary>A query of an [Owned] class without Spec.Reads: it reads only its object's tree (CSV1017).</summary>
        public bool TreeReads;
        /// <summary>The parameters the body assigns (by value): each a local of the body, its value at entry the parameter's.</summary>
        public Dictionary<string, string> AssignedParams = new Dictionary<string, string>();

        // ---- its body: by Lowering (its locals, Checks and Heap add to: the Boogie procedure's)

        public List<KBlock> Blocks = new List<KBlock>();
        public List<KLocal> Locals = new List<KLocal>();
        /// <summary>A lambda's or a local function's: the variables it captures, each some value of its type at entry.</summary>
        public readonly List<(string input, ITypeSymbol type, bool notNull)> Captured = new List<(string, ITypeSymbol, bool)>();
        /// <summary>Their symbols, in the same order (a call of a local function passes their values).</summary>
        public readonly List<ISymbol> CapturedSymbols = new List<ISymbol>();
        /// <summary>The confined locals (their Boogie names): only ever objects the method made, never handed on.</summary>
        public List<string> Confined = new List<string>();
        /// <summary>Each loop head's invariants and measure (by the head's ordinal).</summary>
        public Dictionary<int, List<KSpec>> Invariants = new Dictionary<int, List<KSpec>>();
        /// <summary>A loop without invariants: facts it may keep at its head (the ones that hold on entry and at every back edge).</summary>
        public Dictionary<int, List<KSpec>> Candidates = new Dictionary<int, List<KSpec>>();
        public Dictionary<int, List<KSpec>> Measures = new Dictionary<int, List<KSpec>>();
        /// <summary>Each loop head's last block (by ordinal): the loop is the blocks from the head to it.</summary>
        public Dictionary<int, int> LoopBodies = new Dictionary<int, int>();
        /// <summary>Each loop head's statement (where a loop that exchanges permissions reports).</summary>
        public Dictionary<int, SyntaxNode> LoopSyntax = new Dictionary<int, SyntaxNode>();

        // ---- its effects: by Lowering (Calls), and Heap (Modifies, AnyWrites); BoogieTranslator closes them over calls

        public HashSet<IMethodSymbol> Calls = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
        /// <summary>It calls code whose contract isn't known ($havoc).</summary>
        public bool HavocsAll;
        /// <summary>It calls a delegate, which may change anything.</summary>
        public bool CallsDelegates;
        /// <summary>It awaits ($await).</summary>
        public bool Awaits;
        /// <summary>It reads a collection through an interface: values of the state ($st), declared then.</summary>
        public bool UsesState;
        /// <summary>After Heap: the globals it writes (what it calls is the program's to add).</summary>
        public HashSet<string> Modifies = new HashSet<string>();
        /// <summary>
        /// Of those, the ones it may write at an object allocated before it was called: not only this one's fields in
        /// a constructor, nor a new object's (a field the rest is framed: unchanged at every object allocated before).
        /// </summary>
        public HashSet<string> AnyWrites = new HashSet<string>();

        // ---- what it names, which the printer declares: by Lowering

        /// <summary>The fields it reads or writes (their maps are declared).</summary>
        public HashSet<ISymbol> Fields = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
        /// <summary>The data types it names (their definitions): each case's constructor, fields and tag.</summary>
        public HashSet<INamedTypeSymbol> DataTypes = new HashSet<INamedTypeSymbol>(SymbolEqualityComparer.Default);
        /// <summary>The data types with invariants whose values it takes to be valid.</summary>
        public HashSet<INamedTypeSymbol> Valid = new HashSet<INamedTypeSymbol>(SymbolEqualityComparer.Default);
        /// <summary>The exception types it names (catches, throws, clauses): the program declares them, and how they derive.</summary>
        public HashSet<ITypeSymbol> ExceptionTypes = new HashSet<ITypeSymbol>(SymbolEqualityComparer.Default);
        /// <summary>The classes and interfaces whose dynamic types it tests or makes (KernelTypes.IsModeledClass).</summary>
        public HashSet<ITypeSymbol> ClassTypes = new HashSet<ITypeSymbol>(SymbolEqualityComparer.Default);
        /// <summary>The library's members it calls (list members, by their stub contracts).</summary>
        public HashSet<IMethodSymbol> LibCalls = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
        /// <summary>The collections' models it names.</summary>
        public Dictionary<string, KernelTypes.ModelMap> Models = new Dictionary<string, KernelTypes.ModelMap>();
        /// <summary>The kinds of the dictionaries' pairs it reads (key kind, value kind).</summary>
        public HashSet<(string key, string value)> Pairs = new HashSet<(string, string)>();
        /// <summary>The predicates it names.</summary>
        public HashSet<IMethodSymbol> Preds = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
        /// <summary>The library stubs it uses (functions of the program's).</summary>
        public HashSet<IMethodSymbol> Stubs = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
        /// <summary>The signatures of the delegates it makes, calls or speaks of ($pre, $post, $call of each).</summary>
        public HashSet<string> DelegateKeys = new HashSet<string>();
        /// <summary>Uninterpreted functions it names: their declarations.</summary>
        public HashSet<string> Functions = new HashSet<string>();

        // ---- for reporting: by Lowering (warnings, causes)

        /// <summary>The translation's warnings (CSV1900, not errors): reported if Boogie verifies the method.</summary>
        public List<VerificationDiagnostic> Warnings = new List<VerificationDiagnostic>();
        /// <summary>For the library report: each variable's causes (Lowering.Causes), and the variables its values were made from.</summary>
        public readonly Dictionary<string, HashSet<string>> Causes = new Dictionary<string, HashSet<string>>();
        public readonly Dictionary<string, HashSet<string>> Deps = new Dictionary<string, HashSet<string>>();
    }
}
