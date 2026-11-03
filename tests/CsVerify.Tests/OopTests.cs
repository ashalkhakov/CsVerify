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
    }
}
