using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>Object-oriented code: contracts of abstract members, behavioural subtyping, dynamic types, properties.</summary>
    public class OopTests
    {
        private const string Shapes = @"
public abstract class Shape { [Pure] public abstract long Area(); }
[ContractClassFor(typeof(Shape))]
internal abstract class ShapeContract : Shape { public override long Area() { Spec.Ensures((long r) => r >= 0); return 0; } }
public sealed class Square : Shape
{
    public readonly int Side;
    [Invariant, Pure] public bool Valid() => Side >= 0;
    public Square(int side) { Spec.Requires(side >= 0); Spec.Ensures(Side == side); Side = side; }
    [Pure] public override long Area() => (long)Side * Side;
}
public sealed class Circle : Shape { public readonly int R; [Pure] public override long Area() => R < 0 ? 0 : (long)R * R; }
";

        private static string[] Errors(string method, string body) =>
            Harness.Verify(Shapes + "public static class C { " + body + " }").Errors(method);

        [Fact]
        public void AbstractMembers_TakeTheirContractClass()
        {
            Assert.Empty(Errors("M", "static long M(Shape s) { Spec.Ensures((long r) => r >= 0); return s.Area(); }"));
            Assert.Equal(new[] { "CSV1002" }, Errors("M", "static long M(Shape s) { Spec.Ensures((long r) => r > 0); return s.Area(); }"));
        }

        [Fact]
        public void FinalOverrides_DefineTheQuery_ForTheirInstances()
        {
            Assert.Empty(Errors("M", "static void M() { Shape s = new Square(3); Spec.Assert(s.Area() == 9); }"));
            Assert.Empty(Errors("M", "static void M(Shape s) { if (s is Square q && q.Side == 2) Spec.Assert(s.Area() == 4); }"));
        }

        [Fact]
        public void DynamicTypes_AreDisjointAndExact()
        {
            Assert.Empty(Errors("M", "static void M(Shape s) { if (s is Square) Spec.Assert(!(s is Circle)); }"));
            Assert.Empty(Errors("M", "static void M() { Shape s = new Square(1); Spec.Assert(s is Square && s as Circle == null); }"));
            Assert.Equal(new[] { "CSV1004" }, Errors("M", "static void M(Shape s) { Spec.Assert(s is Square); }"));
        }

        [Fact]
        public void Overrides_HonourTheBaseContract()
        {
            const string bad = @"
public abstract class A { public abstract int F(int x); }
[ContractClassFor(typeof(A))]
internal abstract class AC : A { public override int F(int x) { Spec.Requires(x >= 0); Spec.Ensures((int r) => r >= x); return 0; } }
public sealed class Weaker : A { public override int F(int x) { Spec.Requires(x >= -1); return x < 0 ? 0 : x; } }
public sealed class Stronger : A { public override int F(int x) { Spec.Requires(x >= 5); return x; } }
public sealed class Wrong : A { public override int F(int x) => 0; }";
            var r = Harness.Verify(bad);
            Assert.Empty(r.Errors("Weaker.F"));
            Assert.Equal(new[] { "CSV1018" }, r.Errors("Stronger.F"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong.F"));
        }

        [Fact]
        public void ConstructorChaining_IsACheckedCall()
        {
            const string chain = @"
public class Base { public readonly int X; public Base(int x) { Spec.Requires(x > 0); Spec.Ensures(X == x); X = x; } }
public sealed class Derived : Base { public readonly int Y; public Derived(int x, int y) : base(x) { Spec.Requires(x > 0); Spec.Ensures(X == x && Y == y); Y = y; } }
public sealed class Bad : Base { public Bad() : base(0) { } }
public static class C { static void M() { var d = new Derived(2, 3); Spec.Assert(d.X == 2 && d.Y == 3); } }";
            var r = Harness.Verify(chain);
            Assert.Empty(r.Errors("Derived..ctor"));
            Assert.Empty(r.Errors("M"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("Bad..ctor"));
        }

        [Fact]
        public void Properties_WithCode_AreMethods()
        {
            const string props = @"
public sealed class Box
{
    private int _w;
    [Pure] public int Width { get => _w; set { Spec.Requires(value >= 0); Spec.Ensures(_w == value); _w = value; } }
    [Pure] public int Twice => checked(2 * _w);
}
public static class C {
    static void M(Box b) { b.Width = 3; Spec.Assert(b.Width == 3); }
    static void Bad(Box b) { b.Width = -1; } }";
            var r = Harness.Verify(props);
            Assert.Empty(r.Errors("M"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("Bad"));
            Assert.Equal(new[] { "CSV1010" }, r.Errors("get_Twice")); // a [Pure] getter may not throw
        }

        [Fact]
        public void ImmutableClasses_KeepTheirInvariants() =>
            Assert.Empty(Errors("M", "static void M(Square s) { Spec.Assert(s.Side >= 0); }"));

        [Fact]
        public void AConstructorMayLetThisEscape()
        {
            var r = Harness.Verify(@"
public class Item
{
    public int V;
    public Item(Item[] a) { Spec.Requires(a != null && a.Length > 0); Spec.Ensures(V == 4 && a[0] == this); a[0] = this; V = 4; }
}
public static class U
{
    public static void Make() { var a = new Item[1]; var i = new Item(a); Spec.Assert(i.V == 4 && a[0] == i); }
    public static void MakeBad() { var a = new Item[1]; var i = new Item(a); Spec.Assert(i.V == 5); }
}");
            Assert.Empty(r.Errors("Item..ctor"));
            Assert.Empty(r.Errors("U.Make"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("U.MakeBad"));
        }

        [Fact]
        public void ATargetTypedConditional_AndAnAssignedParameterALambdaReads()
        {
            var r = Harness.Verify(@"
public abstract class Sh { public abstract int A(); }
public sealed class S1 : Sh { public S1() { } public override int A() => 1; }
public sealed class S2 : Sh { public S2() { } public override int A() => 2; }
public static class U
{
    public static Sh Pick(bool c) { Spec.Ensures((Sh r) => r != null); Sh s = c ? new S1() : new S2(); return s; }
    public static int Cap(int x) { Spec.Requires(x == 1); Spec.Ensures((int r) => r == 2); x = x + 1; System.Func<int> f = () => x; return x; }
    public static int CapWrong(int x) { Spec.Requires(x == 1); Spec.Ensures((int r) => r == 1); x = x + 1; System.Func<int> f = () => x; return x; }
}");
            Assert.Empty(r.Errors("U.Pick"));
            Assert.Empty(r.Errors("U.Cap"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("U.CapWrong"));
        }

        // (a parameter a lambda or local function writes: forgotten after each call that may run it, as a local is)
        [Fact]
        public void AParameterALambdaWrites_IsForgottenAfterItRuns()
        {
            var r = Harness.Verify(@"
public static class U
{
    public static int Before(int x) { Spec.Requires(x == 1); System.Action a = () => { x = 5; }; Spec.Assert(x == 1); return x; }
    public static int After(int x) { Spec.Requires(x == 1); System.Action a = () => { x = 5; }; a(); Spec.Assert(x == 1); return x; }
    public static int Local(int x) { Spec.Requires(x == 1); void Set() { x = 7; } Set(); Spec.Assert(x == 1); return x; }
}");
            Assert.Empty(r.Errors("U.Before"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("U.After"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("U.Local"));
        }

        // (-x in a postcondition's lambda reads x: its callers still assume the postcondition)
        [Fact]
        public void ANegationInAPostcondition_IsNoWrite()
        {
            var r = Harness.Verify(@"
public static class U
{
    public static int Abs(int x) { Spec.Requires(x > int.MinValue); Spec.Ensures<int>(r => r >= 0 && (r == x || r == -x)); return x < 0 ? -x : x; }
    public static int Use(int y) { Spec.Ensures<int>(r => r >= 0); return y == int.MinValue ? 0 : Abs(y); }
}");
            Assert.Empty(r.Errors("U.Use"));
        }

        // (a lambda's postcondition of a captured variable it writes: its value at the lambda's return)
        [Fact]
        public void ALambdasPostcondition_OfAVariableItWrites()
        {
            var r = Harness.Verify(@"
public static class U
{
    public static int Inc() { int k = 0; System.Action a = () => { Spec.Ensures(k == Spec.Old(k) + 1); k = k + 1; }; return k; }
    public static int IncBad() { int k = 0; System.Action a = () => { Spec.Ensures(k == Spec.Old(k) + 2); k = k + 1; }; return k; }
}", overflow: false);
            Assert.True(r.Methods.Where(m => m.Name.StartsWith("U.Inc.")).All(m => m.Verified));
            Assert.Contains(r.Methods, m => m.Name.StartsWith("U.IncBad.") && m.Diagnostics.Any(d => d.Id == "CSV1002"));
        }
    }
}
