using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// Lists through their interfaces (IReadOnlyList, IList, IReadOnlyCollection, ICollection): a List's facts cross the
    /// conversion, an array is its cells, and anything else is stable only as long as nothing changes. And the Dictionary
    /// extras (TryAdd, the capacity constructor, Remove with the value out).
    /// </summary>
    public class InterfaceTests
    {
        private const string Common = @"
#nullable enable
using System.Collections.Generic;
public static class Q
{
    public static int First(IReadOnlyList<int> xs) { Spec.Requires(xs.Count > 0); return xs[0]; }
}
";

        [Fact]
        public void ListsAndArrays_KeepTheirFacts_ThroughTheInterfaces()
        {
            var r = Harness.Verify(Common + @"
public static class P
{
    public static int List() { var l = new List<int>(); l.Add(4); return Q.First(l); }
    public static int Array() { var a = new int[] { 1, 2 }; return Q.First(a); }
    public static int Kept(List<int> l) { Spec.Requires(l.Count == 1 && l[0] == 7); Spec.Ensures<int>(r => r == 7); IReadOnlyList<int> xs = l; return xs[0]; }
    public static int Stable(IReadOnlyList<int> xs) { Spec.Requires(xs.Count > 0); var a = xs[0]; Spec.Assert(a == xs[0]); return a; }
    public static int Mutable(IList<int> xs) { Spec.Requires(xs.Count > 1); return xs[1]; }
    public static int Empty() { var l = new List<int>(); return Q.First(l); }
    public static int Unchecked(IReadOnlyList<int> xs) => xs[0];
}");
            Assert.Empty(r.Errors("Q.First"));
            foreach (var m in new[] { "List", "Array", "Kept", "Stable", "Mutable" }) Assert.Empty(r.Errors("P." + m));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("P.Empty"));
            Assert.Equal(new[] { "CSV1003" }, r.Errors("P.Unchecked"));
        }

        [Fact]
        public void AChangeOfTheList_IsSeenThroughTheInterface()
        {
            var r = Harness.Verify(Common + @"
public static class P
{
    // xs may be l: after l.Clear(), xs.Count is not what it was
    public static int Aliased(List<int> l, IReadOnlyList<int> xs) { Spec.Requires(xs.Count > 0); Spec.Modifies(ObjSet.Of(l)); l.Clear(); return xs[0]; }
}");
            Assert.Equal(new[] { "CSV1003" }, r.Errors("P.Aliased"));
        }

        [Fact]
        public void TheProgramsOwnLists_AreUnknownAtEachRead()
        {
            var r = Harness.Verify(Common + @"
public sealed class Mine : IReadOnlyList<int>
{
    public int Count => 1;
    public int this[int i] => i;
    public IEnumerator<int> GetEnumerator() { yield break; }
    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
}
public static class P
{
    public static int Twice(IReadOnlyList<int> xs) { Spec.Requires(xs.Count > 0); var a = xs[0]; Spec.Assert(a == xs[0]); return a; }
}");
            Assert.Contains("CSV1003", r.Errors("Q.First"));
            Assert.Contains("CSV1004", r.Errors("P.Twice"));
        }

        [Fact]
        public void DictionaryExtras()
        {
            var r = Harness.Verify(@"
using System.Collections.Generic;
public static class P
{
    public static int Add() { var d = new Dictionary<string, int>(4); var a = d.TryAdd(""a"", 1); var b = d.TryAdd(""a"", 2); Spec.Assert(a && !b && d.Count == 1); return d[""a""]; }
    public static int First() { Spec.Ensures<int>(r => r == 1); var d = new Dictionary<string, int>(); d.TryAdd(""a"", 1); d.TryAdd(""a"", 2); return d[""a""]; }
    public static int Out() { var d = new Dictionary<int, int>(); d[3] = 9; var ok = d.Remove(3, out var v); Spec.Assert(ok && v == 9 && d.Count == 0); return v; }
}");
            Assert.True(r.Success, string.Join("\n", r.Diagnostics));
        }
    }
}
