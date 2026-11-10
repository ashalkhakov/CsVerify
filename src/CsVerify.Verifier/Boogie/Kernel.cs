using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;

namespace CsVerify.Verifier.Boogie
{
    // The kernel ("idealized C#"): what the passes between Roslyn and Boogie pass along (docs/boogie.md).
    //   Lowering:  Roslyn's control-flow graph -> blocks of kernel statements; C#'s meaning kept in typed nodes
    //              (KArith, KConv, KElem, KLen, KFnCall), checks not yet made
    //   Checks:    each of those nodes -> mathematics, and the asserts (and assumes) it needs, in evaluation order;
    //              well-definedness, postconditions at returns, invariants and measures, termination, non-null arguments
    //   Heap:      arrays -> element maps and allocation; what each procedure modifies
    //   Printer:   Boogie text, and which line is which check

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

    internal abstract class KExpr { }

    /// <summary>A literal, as Boogie writes it ("5", "(-3)", "true", "null").</summary>
    internal sealed class KLit : KExpr
    {
        public string Text;
        public KLit(string text) { Text = text; }
    }

    /// <summary>A variable: a parameter, a local, a quantifier's variable, "result".</summary>
    internal sealed class KVar : KExpr
    {
        public string Name;
        public KVar(string name) { Name = name; }
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
        public KOp(string op, params KExpr[] args) { Op = op; Args = args; }
    }

    /// <summary>forall or exists over an int variable: range ==> body, or range && body.</summary>
    internal sealed class KQuant : KExpr
    {
        public bool Forall;
        public string Var;
        /// <summary>Its variable's Boogie type (int, unless said).</summary>
        public string Type = "int";
        public KExpr Range, Body;
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

    /// <summary>An array's element (a read): checked for null and bounds in code, well-defined if so in a specification.</summary>
    internal sealed class KElem : KExpr
    {
        /// <summary>A string's character (s[i]), not an array's element.</summary>
        public bool String;
        public KExpr Array, Index;
        public ITypeSymbol ArrayType;
        public bool InSpec;
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
    }

    /// <summary>A Boogie statement, as text (what Checks builds of the permission locals).</summary>
    internal sealed class KRaw : KStmt
    {
        public string Text;
    }

    internal abstract class KStmt { }

    internal sealed class KAssign : KStmt
    {
        public string Var;
        public KExpr Value;
        /// <summary>A local of non-nullable type: where its write is checked not null (CSV1014), and its name.</summary>
        public SyntaxNode NotNullAt;
        public string NotNullName;
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

    /// <summary>A write of an array's element (checked for null and bounds, until Checks; a map's, after).</summary>
    internal sealed class KStore : KStmt
    {
        public KExpr Array, Index, Value;
        public ITypeSymbol ArrayType;
        public SyntaxNode At, ArrayAt;
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
        public SyntaxNode At;
        /// <summary>Where each argument is (for a non-null one's check).</summary>
        public SyntaxNode[] ArgsAt;
        public Check Check;
        /// <summary>Where an exception it throws goes, where exceptions are seen (a try's handlers, or the method's exit).</summary>
        public string ThrowsTo;
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
    }

    internal sealed class KHavoc : KStmt
    {
        public string Var;
    }

    /// <summary>Spec.Assert or Spec.Assume, until Checks: well-defined, then asserted (or assumed).</summary>
    internal sealed class KSpecStmt : KStmt
    {
        public KExpr Spec;
        public bool Assume;
        public SyntaxNode At, ArgumentAt;
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
        public KGoto(params string[] targets) { Targets = targets.ToList(); }
    }

    /// <summary>A return, from here (where its postconditions are reported).</summary>
    internal sealed class KReturn : KJump
    {
        public SyntaxNode At;
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
    }

    internal sealed class KLocal
    {
        public string Name;
        public ITypeSymbol Type;
        /// <summary>A Boogie type of its own (a snapshot of a map), in place of Type's.</summary>
        public string Raw;
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

    internal sealed class KSpec
    {
        public KExpr Expr;
        public SyntaxNode At;
        /// <summary>After Checks, for a requires: what a failure of it at a call is about.</summary>
        public Check Check;
    }

    internal sealed class KProcedure
    {
        /// <summary>It calls a delegate, which may change anything; the signatures of the delegates it speaks of.</summary>
        public bool CallsDelegates;
        public HashSet<string> DelegateKeys = new HashSet<string>();
        public IMethodSymbol Method;
        public Contract Contract;
        public MethodResult Result;
        public string Name;
        public bool Ghost;
        public List<IParameterSymbol> Params;
        /// <summary>An instance method or constructor: its receiver is the parameter this.</summary>
        public bool HasThis;
        public bool IsCtor;
        /// <summary>A method of an [Owned] class that isn't [Pure] (or its constructor): it holds this object's view.</summary>
        public bool ThisIsView;
        /// <summary>It holds, gives or checks views: its permissions (perm, object to whether its view is in hand) are kept.</summary>
        public bool UsesPerm;
        /// <summary>A [Predicate]: its body (FunctionBody, its arithmetic as code's) is checked self-framing, once.</summary>
        public bool IsPredicate;
        /// <summary>It keeps cell permissions (cells, cowner): it exchanges some, or names them.</summary>
        public bool UsesCells;
        /// <summary>Its contract names cells: it holds none but those it is given (else every cell, but those it gives away).</summary>
        public bool ArrayMode;
        /// <summary>It keeps single-field permissions (fperm, fowner): the program uses some.</summary>
        public bool UsesFields;
        /// <summary>Its Spec.Modifies: the objects (an ObjSet, a [Ref]bool) whose fields and cells it may write, as of entry.</summary>
        public KExpr Frame;
        /// <summary>A function's Spec.Reads: the objects whose fields and cells its value depends on (a frame axiom says so).</summary>
        public KExpr ReadsFrame;
        /// <summary>An abstract member: a procedure with no body, which calls go to.</summary>
        public bool Abstract;
        /// <summary>An override that states its own precondition: it, and each base's, which must imply it (CSV1018).</summary>
        public List<KExpr> OwnRequires = new List<KExpr>();
        public List<(IMethodSymbol method, List<KExpr> requires)> BaseRequires = new List<(IMethodSymbol, List<KExpr>)>();
        /// <summary>A base's Spec.Modifies, which its own must lie within (CSV1018).</summary>
        public List<(IMethodSymbol method, KExpr frame)> BaseFrames = new List<(IMethodSymbol, KExpr)>();
        /// <summary>Spec.EnsuresOnThrow&lt;E&gt;(Cond): what holds where it leaves by throwing an E.</summary>
        public List<(ITypeSymbol type, KExpr cond, SyntaxNode at)> ThrowEnsures = new List<(ITypeSymbol, KExpr, SyntaxNode)>();
        /// <summary>The exception types it names (catches, throws, clauses): the program declares them, and how they derive.</summary>
        public HashSet<ITypeSymbol> ExceptionTypes = new HashSet<ITypeSymbol>(SymbolEqualityComparer.Default);
        /// <summary>Each loop head's statement (where a loop that exchanges permissions reports).</summary>
        public Dictionary<int, SyntaxNode> LoopSyntax = new Dictionary<int, SyntaxNode>();
        /// <summary>The predicates it names.</summary>
        public HashSet<IMethodSymbol> Preds = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
        /// <summary>The library stubs it uses (functions of the program's).</summary>
        public HashSet<IMethodSymbol> Stubs = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
        /// <summary>The fields it reads or writes (their maps are declared).</summary>
        public HashSet<ISymbol> Fields = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
        public List<KLocal> Locals = new List<KLocal>();
        public List<KSpec> Requires = new List<KSpec>(), Ensures = new List<KSpec>();
        /// <summary>Spec.Decreases of the method: its parameters' measure.</summary>
        public List<KExpr> Decreases;
        /// <summary>Each loop head's invariants and measure (by the head's ordinal).</summary>
        public Dictionary<int, List<KSpec>> Invariants = new Dictionary<int, List<KSpec>>();
        public Dictionary<int, List<KSpec>> Measures = new Dictionary<int, List<KSpec>>();
        /// <summary>Each loop head's last block (by ordinal): the loop is the blocks from the head to it.</summary>
        public Dictionary<int, int> LoopBodies = new Dictionary<int, int>();
        /// <summary>A [Pure] or [GhostFunction] method of one expression: a function too, of this body.</summary>
        public KExpr FunctionBody;
        public List<KBlock> Blocks = new List<KBlock>();
        /// <summary>After Checks: the asserts at entry (the preconditions well-defined).</summary>
        public List<KStmt> Entry = new List<KStmt>();
        public HashSet<IMethodSymbol> Calls = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
        /// <summary>After Heap: the globals it writes (what it calls is the program's to add).</summary>
        public HashSet<string> Modifies = new HashSet<string>();
        /// <summary>
        /// Of those, the ones it may write at an object allocated before it was called: not only this one's fields in
        /// a constructor, nor a new object's (a field the rest is framed: unchanged at every object allocated before).
        /// </summary>
        public HashSet<string> AnyWrites = new HashSet<string>();
        public int Obligations;
    }
}
