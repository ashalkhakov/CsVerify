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
        public KExpr Array, Index;
        public ITypeSymbol ArrayType;
        public bool InSpec;
        public SyntaxNode At, ArrayAt;
    }

    /// <summary>An array's length.</summary>
    internal sealed class KLen : KExpr
    {
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

    // ------------------------------------------------------------------ statements

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
    }

    internal sealed class KAssert : KStmt
    {
        public KExpr Cond;
        public Check Check;
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
