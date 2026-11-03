# A validated LR(1) parser for CsLemon

CsLemon builds an LALR(1) automaton from a grammar; nothing verified says the automaton parses the grammar's language.
Following the approach of Jourdan, Pottier and Leroy, *Validating LR(1) Parsers* (ESOP 2012), we do not verify the
construction. We verify an LR interpreter once, and validate each automaton CsLemon builds against its grammar. This
code is written from the paper's description (not from any implementation of it), in C#, and verified with CsVerify.

## Grammar and automaton

- **Symbols** are numbered: terminals `0 .. NTerm-1` (0 is Lemon's end of input, `$`), nonterminals
  `NTerm .. NSym-1`. `Start` is the start symbol.
- **Rules** `r`: a left-hand side `Lhs[r]` (a nonterminal) and a right-hand side, a sequence of symbols.
- A **parse tree** is a leaf (a terminal) or a node (a rule, and one tree per symbol of its right-hand side). A tree
  is *valid for* a symbol X when it is a leaf X, or a node of a rule whose left-hand side is X and whose children are
  valid for the rule's right-hand-side symbols, in order. Its *fringe* is the sequence of its leaves. `X` derives `w`
  when some tree valid for X has fringe w (the paper's semantics of grammars, with the parse tree as semantic value).
- **States** `0 .. NState-1`; state 0 is the initial state. Every other state has an incoming symbol `Incoming[s]`.
- The **action table** maps every (state, terminal) to *shift s'*, *reduce r*, *accept* or *reject*. The **goto
  table** maps (state, nonterminal) to a state, or is undefined. A shift on `a` goes to a state whose incoming symbol is
  `a`, a goto on `A` to one whose incoming symbol is `A` (checked when the automaton is built).

Lemon's automaton is exported in this form: its states, and its actions after conflict resolution but before table
compression. Lemon accepts by an ACCEPT entry for the start symbol in state 0, acting as a goto; here that becomes one
extra state, the goto of state 0 on the start symbol, whose incoming symbol is the start symbol and whose action on `$`
is accept.

## The interpreter

The input is a finite sequence of terminals other than `$`; past its end, the lookahead is `$`. The stack is a list of
cells (state, parse tree), the current state being the top cell's, or 0 when the stack is empty. With `fuel` steps:

- *shift s'*: push (s', leaf a), consume a;
- *reduce r*, with a right-hand side `X1 .. Xn`: pop n cells, checking that the i-th popped from the bottom has the
  incoming symbol `Xi`; build the node of r over their trees; push (goto(current, Lhs[r]), node). A missing cell, a
  failed check or an undefined goto is an **internal error**;
- *accept*: pop one cell, checking that its incoming symbol is `Start` and that the stack is then empty (an internal
  error otherwise); the result is its tree;
- *reject*: the input is not in the language;
- no fuel left: *out of fuel*.

## What is proved

1. **Soundness** (paper, Theorem 1), for every automaton: if the interpreter accepts the input with tree t, then t is
   valid for `Start` and its fringe is the input. The invariant: every cell's tree is valid for its state's incoming
   symbol, and the fringes of the cells' trees, bottom to top, are the input consumed so far.
2. **Safety** (Theorem 2): if the automaton passes the safety validator, the interpreter never reaches an internal
   error. The validator is given, for each state σ, `pastSymbols(σ)` and `pastStates(σ)`: a description of what lies
   under σ on any stack (the symbols, and a superset of the states, of the topmost cells below it). The invariant
   *safe*: for each cell, the description of its state is a suffix of the cells below it (symbols equal, state sets
   containing the actual states). The validator checks:
   - for every transition (shift or goto) on X from σ to σ': `pastSymbols(σ')` is a suffix of
     `pastSymbols(σ) incoming(σ)`, and `pastStates(σ')` is a suffix (by superset) of `pastStates(σ) {σ}`;
   - for every *reduce A → α* in σ: α is a suffix of `pastSymbols(σ) incoming(σ)`, and the goto on A is defined in
     every state of the set k = |α| deep in `pastStates(σ) {σ}` (every state at all, if that is deeper than known);
   - for every *accept* in σ: σ is not initial, its incoming symbol is `Start`, and `pastStates(σ)` is `{0}`.

   The annotations are computed by CsLemon (unverified); only their checking is trusted.
3. **Completeness** (Theorem 3): if the automaton passes the completeness validator and the input is in the language,
   the interpreter, with enough fuel, accepts it. The validator is given each state's LR(1) items (rule, dot,
   lookahead set: Lemon's configurations and follow sets) and the first sets and nullable flags, and checks that the
   first/nullable sets are a fixed point of their equations, that item sets are closed, that each item has the shift,
   goto or reduce it calls for, and that the initial state has the start items and the accepting state accepts.
   Conflicts Lemon resolved (by precedence) make it fail for the items involved; those are reported.
4. **The compressed tables**: looking up (state, lookahead) in Lemon's `yy_action`/`yy_lookahead` tables gives the
   action the automaton has there.

Termination is not proved: the interpreter takes fuel (the paper explains why: unit and empty rules do not shrink the
stack, and automata whose interpretation loops exist).

## Completeness, as proved here

The interpreter is a pure function `Step` (one action) iterated by the ghost `Steps(n, run)`; `Parse` runs `Step` in
a loop. Completeness is a lemma about `Steps`, by induction on the parse tree (the paper's intuition: the parser
walks the tree depth-first, shifting at leaves and reducing at nodes):

- **Items.** The validator is given, per state, items (rule, dot, lookahead set) — Lemon's configurations and their
  follow sets — and first sets and nullable flags. `Has(σ, r, d, c)`: some item of σ is (r, d) with c in its set.
- **Walk(t)**: if t is a tree for the symbol after the dot of an item (r, d, b) of the top state σ, the input at pos
  begins with t's fringe, and the terminal after it is in first(rhs[d+1..] b), then `Steps(Size(t))` pushes exactly
  t, in a state having (r, d+1, b). For a leaf: one shift. For a node of rule r': closure gives (r', 0, la) in σ;
  `WalkKids` pushes the children one by one; the reduce on la pops them (the incoming-symbol checks pass: an item
  (r, d) with d > 0 says its state's incoming symbol is rhs[d-1]) and the goto pushes the node.
- **The root**: the start rules' items with lookahead `$` are in state 0, and after the root's children the reduce,
  the goto to the accepting state and the accept follow: `Steps(Size(t) + 1)` from the empty stack accepts t itself
  (so a validated grammar is unambiguous).

Validator conditions (the paper's, adapted to Lemon): first/nullable are closed under the rules; item sets are
closed; every item (r, d) with d at the end reduces r on its lookaheads; with a terminal (or multiterminal) after
the dot, shifts on it (each member) to a state having (r, d+1) with the same lookaheads; with a nonterminal, has a
goto (defined: stricter than the paper's, so no appeal to safety is needed) to such a state; an item (r, d) with
d > 0 makes rhs[d-1] its state's incoming symbol; state 0 has every start rule at dot 0 with lookahead `$`; the goto
of state 0 on the start symbol accepts on `$`.

Conflicts resolved by precedence (`%left`, `%right`, `%nonassoc`) drop actions some items call for, and the
validator rejects the automaton: such grammars are ambiguous, and the parser deliberately does not accept every tree.
