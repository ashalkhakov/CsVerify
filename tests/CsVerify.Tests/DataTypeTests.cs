using Xunit;

namespace CsVerify.Tests
{
    /// <summary>Closed positional record hierarchies as algebraic data types, and object invariants.</summary>
    public class DataTypeTests
    {
        private const string ListType = @"
public abstract record List
{
    private List() { }
    public sealed record Nil() : List;
    public sealed record Cons(int Head, List Tail) : List;
}
";
        private const string LemmaAttrs = "[Lemma, Conditional(\"CSVERIFY_SPEC\")] ";

        private const string ListFunctions = @"
    [GhostFunction] public static int Length(List xs)
    {
        Spec.Decreases(xs);
        Spec.Ensures((int r) => r >= 0);
        return xs switch { List.Nil => 0, List.Cons c => 1 + Length(c.Tail) };
    }
    [Pure] public static List Append(List xs, List ys)
    {
        Spec.Decreases(xs);
        return xs switch { List.Nil => ys, List.Cons c => new List.Cons(c.Head, Append(c.Tail, ys)) };
    }
";

        private static string[] Errors(string method, string source) =>
            Harness.Verify(ListType + "public static class C { " + ListFunctions + source + " }").Errors(method);

        [Fact]
        public void StructuralRecursion_Terminates()
        {
            Assert.Empty(Errors("Length", ""));
            Assert.Empty(Errors("Append", ""));
            // recursing on the whole value is not structural
            Assert.Equal(new[] { "CSV1008" }, Errors("Bad", "[Pure] static int Bad(List xs) { Spec.Decreases(xs); return xs is List.Cons ? Bad(xs) : 0; }"));
        }

        [Fact]
        public void StructuralInduction_ProvesLemmas()
        {
            const string lemma = LemmaAttrs + @"static void AppendLength(List xs, List ys)
            {
                Spec.Decreases(xs);
                Spec.Ensures(Length(Append(xs, ys)) == Length(xs) + Length(ys));
                if (xs is List.Cons c) CALL;
            }";
            Assert.Empty(Errors("AppendLength", lemma.Replace("CALL", "AppendLength(c.Tail, ys)")));
            Assert.Equal(new[] { "CSV1002" }, Errors("AppendLength", lemma.Replace("CALL", "Spec.Assert(true)")));
        }

        [Fact]
        public void Switch_MustCoverEveryCase()
        {
            // in a definition, falling off the switch throws (CSV1011); in a specification it is ill-defined (CSV1012)
            Assert.Equal(new[] { "CSV1011" }, Errors("Head", "[Pure] static int Head(List xs) { return xs switch { List.Cons c => c.Head }; }"));
            Assert.Empty(Errors("Head", "[Pure] static int Head(List xs) { Spec.Requires(xs is List.Cons); return xs switch { List.Cons c => c.Head }; }"));
            Assert.Equal(new[] { "CSV1012" }, Errors("M", "static void M(List xs) { Spec.Requires((xs switch { List.Nil => 0 }) == 0); }"));
        }

        [Fact]
        public void Downcasts_InProofs_MustBeShown()
        {
            // in code a failed cast throws, so what follows may assume it; a definition or lemma may not throw
            Assert.Equal(new[] { "CSV1011" }, Errors("Head", "[Pure] static int Head(List xs) => ((List.Cons)xs).Head;"));
            Assert.Empty(Errors("Head", "[Pure] static int Head(List xs) { Spec.Requires(xs is List.Cons); return ((List.Cons)xs).Head; }"));
            Assert.Empty(Errors("M", "static int M(List xs) { var c = (List.Cons)xs; Spec.Assert(xs is List.Cons); return c.Head; }"));
        }

        [Fact]
        public void Construction_IsAValue()
        {
            Assert.Empty(Errors("M", @"static void M() {
                var l = new List.Cons(1, new List.Nil());
                Spec.Assert(l.Head == 1 && l.Tail is List.Nil);
                Spec.Assert(Length(l.Tail) == 0 && Length(l) == 1); // [Pure] unfolds one level per use
                Spec.Assert(l == new List.Cons(1, new List.Nil()));
                Spec.Assert(l != new List.Cons(2, new List.Nil()));
                Spec.Assert(new List.Nil() != (List)l); }"));
            Assert.Empty(Errors("M", "static void M(List.Cons a, List.Cons b) { Spec.Requires(a.Head == b.Head && a.Tail == b.Tail); Spec.Assert(a == b); }"));
            Assert.Empty(Errors("M", "static int M(List xs) => xs is List.Cons(var h, List.Nil) ? h : 0;"));
        }

        [Fact]
        public void DataValues_HaveNoIdentity()
        {
            // two allocations are different objects at run time: only value equality is modeled, never reference equality
            Assert.Equal(new[] { "CSV1004" }, Errors("M", "static void M() { object a = new List.Nil(); object b = new List.Nil(); Spec.Assert(a == b); }"));
            Assert.Equal(new[] { "CSV1004" }, Errors("M", "static void M() { object a = new List.Nil(); object b = new List.Nil(); Spec.Assert(a != b); }"));
        }

        [Fact]
        public void OpenHierarchy_HasNoKnownCases() =>
            Assert.Equal(new[] { "CSV1011" }, Harness.Verify(@"
public abstract record Shape { public sealed record Dot() : Shape; }
public static class C { [Pure] static int K(Shape s) => s switch { Shape.Dot => 0 }; }").Errors("K"));

        [Fact]
        public void PositionalFields_KeepTheirNullability()
        {
            const string named = "public sealed record Named(string Name); public static class C { BODY }";
            Assert.Empty(Harness.Verify(named.Replace("BODY", "static int L(Named n) => n.Name.Length;")).Errors("L"));
            Assert.Equal(new[] { "CSV1014" }, Harness.Verify(named.Replace("BODY", "static Named M() => new Named(null!);")).Errors("M"));
        }

        private const string Range = @"
public sealed record Range(int Lo, int Hi)
{
    [Invariant, Pure] public bool Valid() => Lo <= Hi;
    [Pure] public long Width() { Spec.Ensures((long r) => r >= 0); return (long)Hi - Lo; }
}
";

        [Fact]
        public void Invariant_IsProvedAtConstruction()
        {
            string Check(string body) => string.Join(",", Harness.Verify(Range + "public static class C { " + body + " }").Errors("M"));
            Assert.Equal("CSV1015", Check("static Range M() => new Range(2, 1);"));
            Assert.Equal("", Check("static Range M(int a) { Spec.Requires(a >= 0); return new Range(-a, a); }"));
        }

        [Fact]
        public void Invariant_HoldsOfEveryObject()
        {
            var r = Harness.Verify(Range + "public static class C { static long M(Range r) { Spec.Ensures((long w) => w >= 0); return (long)r.Hi - r.Lo; } }");
            Assert.Empty(r.Errors("M"));
            Assert.Empty(r.Errors("Width"));
        }

        [Fact]
        public void Invariant_CannotProveItself()
        {
            // Check is what the invariant is made of: verifying it may not assume the invariant
            var r = Harness.Verify(@"
public sealed record Range(int Lo, int Hi)
{
    [Invariant, Pure] public bool Valid() => Check();
    [Pure] public bool Check() { Spec.Ensures((bool b) => b); return Lo <= Hi; }
}");
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Check"));
        }

        [Fact]
        public void Invariants_MayNotReadMutableState()
        {
            // a mutable cell can be changed after the record is built, by anyone holding it: the invariant would lie
            var r = Harness.Verify(@"
public sealed class Cell { public int Val; }
public sealed record Holder(Cell C) { [Invariant, Pure] public bool Pos() => C.Val > 0; }
public static class C { static void Use(Holder h) { Spec.Assert(h.C.Val > 0); } }");
            Assert.Equal(new[] { "CSV1015" }, r.Errors("Pos"));
            // positional fields and pure functions of them are fine (the trees, Interval, FACT rely on it)
            Assert.Empty(Harness.Verify(Range).Errors("Valid"));
        }

        [Fact]
        public void ConstructorPreconditions_AreCheckedAtNew()
        {
            const string box = "public sealed class Box { public Box(int x) { Spec.Requires(x > 0); } } public static class C { BODY }";
            Assert.Equal(new[] { "CSV1001" }, Harness.Verify(box.Replace("BODY", "static Box M() => new Box(0);")).Errors("M"));
            Assert.Empty(Harness.Verify(box.Replace("BODY", "static Box M() => new Box(1);")).Errors("M"));
        }
    
        private const string Generic = @"
public abstract record List<T>
{
    private List() { }
    public sealed record Nil() : List<T>;
    public sealed record Cons(T Head, List<T> Tail) : List<T>;
}
internal abstract record Option<T>;
internal sealed record None<T>() : Option<T>;
internal sealed record Some<T>(T Value) : Option<T>;
internal static class C {
    [GhostFunction] public static int Length<T>(List<T> xs) { Spec.Decreases(xs); Spec.Ensures((int r) => r >= 0); return xs switch { List<T>.Nil => 0, List<T>.Cons c => 1 + Length(c.Tail) }; }
    [Pure] public static List<T> Append<T>(List<T> xs, List<T> ys) { Spec.Decreases(xs); return xs switch { List<T>.Nil => ys, List<T>.Cons c => new List<T>.Cons(c.Head, Append(c.Tail, ys)) }; }
    [Lemma, Conditional(""CSVERIFY_SPEC"")] static void AppendLength<T>(List<T> xs, List<T> ys) { Spec.Decreases(xs); Spec.Ensures(Length(Append(xs, ys)) == Length(xs) + Length(ys)); if (xs is List<T>.Cons c) AppendLength(c.Tail, ys); }
    [Pure] static Option<T> Nth<T>(List<T> xs, int n) { Spec.Decreases(xs); return xs switch { List<T>.Cons c => n == 0 ? new Some<T>(c.Head) : Nth(c.Tail, n - 1), _ => new None<T>() }; }
    BODY
}";

        private static string[] GenericErrors(string method, string body) => Harness.Verify(Generic.Replace("BODY", body)).Errors(method);

        [Fact]
        public void GenericDataTypes_AreOneTypeForAllInstantiations()
        {
            var r = Harness.Verify(Generic.Replace("BODY", ""));
            Assert.Empty(r.Errors("Length"));
            Assert.Empty(r.Errors("Append"));
            Assert.Empty(r.Errors("AppendLength"));
            // a List<int> built here is what the generic functions and lemmas take apart
            Assert.Empty(GenericErrors("M", @"static void M() {
                var l = new List<int>.Cons(5, new List<int>.Nil());
                Spec.Assert(Length(l.Tail) == 0 && Length(l) == 1);
                AppendLength(l, l);
                Spec.Assert(Length(Append(l, l)) == 2); }"));
        }

        [Fact]
        public void GenericCases_NeedNotBeNested()
        {
            Assert.Empty(GenericErrors("NthInRange", @"[Lemma, Conditional(""CSVERIFY_SPEC"")] static void NthInRange<T>(List<T> xs, int n) {
                Spec.Requires(0 <= n && n < Length(xs)); Spec.Decreases(xs); Spec.Ensures(Nth(xs, n) is Some<T>);
                if (xs is List<T>.Cons c && n > 0) NthInRange(c.Tail, n - 1); }"));
            Assert.Empty(GenericErrors("Get", "static int Get(Option<int> o) => o switch { Some<int> s => s.Value, None<int> => 0 };"));
        }

        [Fact]
        public void GenericEquality_FollowsTheTypeArgument()
        {
            Assert.Empty(GenericErrors("M", @"static void M() {
                Spec.Assert(new List<int>.Cons(5, new List<int>.Nil()) == new List<int>.Cons(5, new List<int>.Nil()));
                Spec.Assert(new List<int>.Cons(5, new List<int>.Nil()) != new List<int>.Cons(6, new List<int>.Nil())); }"));
            // strings compare by contents, which the verifier does not model: unknown, not wrong
            Assert.Equal(new[] { "CSV1002" }, GenericErrors("M", "static bool M(List<string> a, List<string> b) { Spec.Ensures((bool r) => r == (a == b)); return a == b; }"));
        }

        [Fact]
        public void GenericElements_AreMaybeNull()
        {
            // generic code can build a List<string> holding null (T is unconstrained), so Head is not known non-null
            Assert.Equal(new[] { "CSV1013" }, GenericErrors("M", "static int M(List<string>.Cons c) => c.Head.Length;"));
            Assert.Empty(GenericErrors("M", "static int M(List<string?>.Cons c) => c.Head == null ? 0 : c.Head.Length;"));
        }
}
}
