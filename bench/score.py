"""Scores the linter benchmark: reads diagnostics (file(line,col): warning|error ID: ...) on stdin, the cases'
regions from the file given, and prints a Markdown table of which tool reported which case."""
import collections, re, sys

# The rules that speak of each case's bug, by tool. Only these count: the others (style, naming, culture) fire all over
# the cases and say nothing about the bug (their totals are listed as noise).
RULES = {
    "ThrowNull": {"SS006", "CS8597", "CA2201", "NULLPTR_DEREFERENCE"},
    "ModifiedWhileEnumerated": {"SS057"},
    "Unobserved": {"CS4014", "MA0134", "CA2012"},
    "Disposal": {"CA2000", "IDE0067", "PULSE_RESOURCE_LEAK"},
    "DisposableField": {"SS066", "CA2213", "CA1001", "PULSE_RESOURCE_LEAK"},
    "FormatArguments": {"SS014", "CA2241", "MA0183"},
    "SwitchExpression": {"CS8509", "CS8524", "SS018"},
    "NaNComparison": {"MA0082", "CA2242", "RCS1215"},
    "UnusedResult": {"SS040", "MA0060", "CA1806"},
    "OrderByTwice": {"SS055", "MA0030"},
    "TimeSpanTicks": {"SS068"},
    "BlockingResult": {"SS034", "SS035", "MA0042", "MA0045"},
    "IdenticalBranches": {"MA0140", "RCS1211"},
    "Null": {"CS8602", "CS8600", "CS8603", "CS8604", "MA0191", "NULLPTR_DEREFERENCE"},  # (CA1062 is about the arguments, not this)
    "Bounds": set(),
    "Overflow": set(),
    "DivideByZero": set(),
    "StringIndex": set(),
    "Substring": set(),
    "MaskedIndex": set(),
    "Truncation": set(),
    "Race": {"THREAD_SAFETY_VIOLATION"},
}
TOOLS = [("compiler", "CS"), ("SDK (CA)", "CA"), ("SharpSource", "SS"), ("Meziantou", "MA"), ("Roslynator", "RCS"),
         ("StyleCop", "SA"), ("InferSharp", "INFER"), ("CsVerify", "CSV")]
# (InferSharp's issue types are words, not a prefix and a number)
INFER = {"NULLPTR_DEREFERENCE", "PULSE_RESOURCE_LEAK", "DOTNET_RESOURCE_LEAK", "THREAD_SAFETY_VIOLATION", "TAINT_ERROR"}

def tool(rule):
    if rule in INFER:
        return "InferSharp"
    for name, prefix in sorted(TOOLS, key=lambda t: -len(t[1])):
        if rule.startswith(prefix) and rule[len(prefix):].isdigit():
            return name
    return None

cases, current = [], None
for i, line in enumerate(open(sys.argv[1], encoding="utf-8"), 1):
    m = re.match(r"\s*#region case (\S+) (bug|ok)", line)
    if m:
        current = [m.group(1), m.group(2) == "bug", i, None]
    elif current and line.strip() == "#endregion":
        current[3] = i
        cases.append(current)
        current = None

found = set()
for line in sys.stdin:
    m = re.search(r"Cases\.cs\((\d+),\d+\): (warning|error) ([A-Z_]+\d*)", line)
    if m:
        # CsVerify's warnings say what it does not model, not what is wrong
        if m.group(3).startswith("CSV") and m.group(2) != "error":
            continue
        found.add((int(m.group(1)), m.group(3)))

hits = collections.defaultdict(set)  # (case, tool) -> rules
noise = collections.Counter()
for ln, rule in found:
    t = tool(rule)
    if t is None:
        continue
    case = next((c for c in cases if c[2] <= ln <= c[3]), None)
    family = case[0].split(".")[0] if case else None
    if t == "CsVerify" or (case and rule in RULES.get(family, set())):
        if case:
            hits[(case[0], t)].add(rule)
    else:
        noise[t] += 1

names = [t for t, _ in TOOLS]
print("| case | bug? | " + " | ".join(names) + " |")
print("|---|---|" + "---|" * len(names))
for name, bug, _, _ in cases:
    cells = [", ".join(sorted(hits[(name, t)])) or "·" for t in names]
    print(f"| {name} | {'bug' if bug else 'no'} | " + " | ".join(cells) + " |")
bugs = [c for c in cases if c[1]]
oks = [c for c in cases if not c[1]]
print("| **bugs reported** | " + str(len(bugs)) + " | " +
      " | ".join(str(sum(1 for c in bugs if hits[(c[0], t)])) for t in names) + " |")
print("| **harmless code reported** | " + str(len(oks)) + " | " +
      " | ".join(str(sum(1 for c in oks if hits[(c[0], t)])) for t in names) + " |")
print("| **other warnings** (noise) | | " + " | ".join(str(noise[t]) for t in names) + " |")
any_tool = sum(1 for c in bugs if any(hits[(c[0], t)] for t in names))
print(f"\nBugs reported by some tool: {any_tool} of {len(bugs)}.")
