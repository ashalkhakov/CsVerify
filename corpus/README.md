# The corpus

What CsVerify is measured on (Phase 0 of [the plan](https://github.com/ashalkhakov/CsVerify/issues/9)):

| program | what it is | specifications |
|---|---|---|
| `Json/Jsmn.cs` | [jsmn](https://github.com/zserge/jsmn), a JSON tokenizer, ported from C (default configuration) | none |
| `Http/PicoHttpParser.cs` | [picohttpparser](https://github.com/h2o/picohttpparser): HTTP/1.x requests, responses, headers and chunked decoding, ported from C over `ReadOnlySpan<byte>` | none |
| [`samples/Good`](../samples/Good) | the samples | full: they verify |
| [CsLemon](../lemon/README.md) | the LEMON parser generator, ported from C | full: it verifies |

The two parsers are code as people write it, with no specifications and no reference to CsVerify. They are what the
verifier has to get through with no help. The ports keep the C's structure: pointers become offsets, and the C's
`*ret = -1; return NULL` becomes a negative return value. Both originals are MIT-licensed, and their notices are in
the files. `CorpusTests` checks the ports against cases from the originals' own tests.

## The library report

```bash
bash corpus/report.sh
```

This verifies each program on its own (`--each`) and prints the [library report](../docs/running.md#the-library-report).
CI runs it too (the `library-report` job), with the report in the job's summary.

## The backlog (2026-11-04)

The corpus has 798 methods: 784 verify, 13 have failed obligations, and 1 is not verified because of an unsupported
construct. All 95 failed obligations are in the two parsers. The samples and CsLemon verify, but the report still
lists what they call without contracts.

What the failures come from (one may have several causes):

| failures | cause |
|---:|---|
| 76 | a loop without invariants |
| 15 | a call to a method of the program without postconditions (`Jsmn.AllocToken` 5, `PicoHttpParser.GetTokenToEol` 3, …) |
| 1 | a library member without a contract (`CharEnumerator.Current`, from `foreach` over a string) |
| 8 | none of these: the code's own values |

By kind: 49 overflow (CSV1010), 45 index out of range (CSV1003), 1 null dereference (CSV1013). One construct is
unsupported: passing an array element's field by `out` (`out headers[n].NameStart`). Among the unknown values
(CSV1900), the most common by far is `operator on String is not modeled` (463, nearly all in CsLemon), then
`Console`'s properties (27).

What it says about the order of the plan:
1. **Loops come first.** 80% of the failures are a loop's unknown state at its head: a counter whose range is
   lost, a cursor that might have passed the end. The plan has no item for this. Phase 1 needs facts about loops
   without invariants: the bounds a `for` loop's condition and step give, and what a loop leaves unchanged.
2. **Then calls inside the program.** Small private methods without postconditions (`AllocToken`, `GetTokenToEol`)
   cost their callers every fact about their results. Inferring their postconditions, or inlining them, is the next
   lever.
3. **Language coverage:** `out` to an array element's field.
4. **Library contracts matter less here than expected.** The parsers call little of the library. Span's `Slice` and
   `CopyTo` (Phase 5) cause no failures yet, only because nothing around them is known. Strings' `==` (Phase 4) is
   the largest group of unknown values.

### After Phase 1 (check profiles, language coverage)

With every check on, the numbers are as above: Phase 1 adds no loop facts. The `out` to an array element's field is
supported now, but this callee, `ParseToken`, reads a span, so the cell is still refused (the callee could see it).
With `--checks null` both parsers verify: 21 of 21 methods, with 1213 obligations of other kinds assumed and the 2
`out` arguments treated as unknown values. One false alarm on the way was fixed: a `static readonly` array set by a
method call (`TokenCharMap = BuildTokenCharMap()`) is not null.

### After the loop facts

Facts inferred for loops without invariants (see [How it works](../docs/how-it-works.md)) take the parsers from 95
failed obligations to 87: loops without invariants now cause 69 of them, down from 76. The rest are mostly real. Like
the C, jsmn's `Parse` trusts its caller and the state of its parser. Nothing says `len <= js.Length`, or
`numTokens <= tokens.Length`, or that `Pos`, `TokNext` and `TokSuper`, left by earlier calls, are in range. Those are
preconditions and an object invariant to write, or to infer from the methods' callers.

### After the span model (Phase 5)

A span's cells are tracked now, and its `Slice` and `CopyTo` ranges are checked as C# checks them. Before, those were
library calls without contracts, so a bad range was a possible exception, not a failure. The parsers' failures go
from 87 to 93. The new ones are 9 range checks in `DecodeChunked`, and they are real: nothing relates `bufSize`, which
the caller passes by reference, to `buf.Length`. The C takes the buffer's size on trust the same way.

The stubs themselves are checked against the BCL: see
[Conformance tests](../docs/library-contracts.md#conformance-tests).
