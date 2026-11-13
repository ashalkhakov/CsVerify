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
        public void SearchesWritesAndForeach_ThroughTheInterfaces()
        {
            var r = Harness.Verify(Common + @"
public static class P
{
    public static bool Has(IList<int> l) { Spec.Requires(l.Count == 2 && l[0] == 3 && l[1] == 4); Spec.Ensures<bool>(r => r); return l.Contains(4); }
    public static int Index(IList<string> l) { Spec.Requires(l.Count == 2 && l[0] == ""a"" && l[1] == ""b""); Spec.Ensures<int>(r => r == 1); return l.IndexOf(""b""); }
    public static void Add(List<int> list) { Spec.Requires(list.Count == 0); Spec.Modifies(ObjSet.Of(list)); IList<int> l = list; l.Add(5); Spec.Assert(list.Count == 1 && list[0] == 5); }
    public static void Set(int[] a) { Spec.Requires(a.Length == 2); IList<int> l = a; l[1] = 9; Spec.Assert(a[1] == 9); }
    public static void SetList(List<int> list) { Spec.Requires(list.Count == 2); Spec.Modifies(ObjSet.Of(list)); IList<int> l = list; l[0] = 7; Spec.Assert(list[0] == 7 && list.Count == 2); }
    public static void Removed(List<int> list)
    {
        Spec.Requires(list.Count == 2 && list[0] == 1 && list[1] == 2);
        Spec.Modifies(ObjSet.Of(list));
        ICollection<int> c = list;
        var ok = c.Remove(1);
        Spec.Assert(ok && list.Count == 1 && list[0] == 2);
    }
    // an array is fixed-size: Add throws, so nothing after it runs
    public static void ArrayAdd(int[] a) { IList<int> l = a; l.Add(1); Spec.Assert(false); }
    public static int Each(IReadOnlyList<int> xs) { int s = 0; foreach (var x in xs) { Spec.Assert(x == xs[Spec.Index(x)]); s = x; } return s; }
    public static int Count(IList<int> xs) { Spec.Ensures<int>(r => r == xs.Count); int n = 0; foreach (var x in xs) { Spec.Invariant(n == Spec.Index(x)); n = n + 1; } return n; }
    // false claims: il may be a; c may be any collection
    public static void Alias(int[] a, IList<int> il) { Spec.Requires(a.Length > 0 && a[0] == 1 && il.Count > 0); il[0] = 5; Spec.Assert(a[0] == 1); }
    public static void Anything(ICollection<int> c) { Spec.Requires(c.Count == 0); c.Add(1); Spec.Assert(c.Count == 1); }
}", overflow: false);
            foreach (var m in new[] { "Has", "Index", "Add", "Set", "SetList", "Removed", "ArrayAdd", "Each", "Count" }) Assert.Empty(r.Errors("P." + m));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("P.Alias"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("P.Anything"));
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

        [Fact]
        public void ExplicitImplementations_KeepTheInterfacesContract()
        {
            var r = Harness.Verify(@"
public interface ICounter { int Next(); }
[ContractClassFor(typeof(ICounter))]
internal abstract class CounterContract : ICounter { public int Next() { Spec.Ensures<int>(r => r > 0); return default; } }
public class One : ICounter { int ICounter.Next() { return 1; } }
public class Zero : ICounter { int ICounter.Next() { return 0; } }
public static class P { public static int Ask(ICounter c) { Spec.Ensures<int>(r => r > 0); return c.Next(); } }");
            Assert.Empty(r.Errors("One.ICounter.Next"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Zero.ICounter.Next"));
            Assert.Empty(r.Errors("P.Ask"));
        }

        [Fact]
        public void OtherMembersAndForeach_ThroughTheInterfaces()
        {
            var r = Harness.Verify(Common + @"
public static class P
{
    public static bool Has(ICollection<int> l) { Spec.Requires(l != null); return l.Contains(3); }
    public static int Last(IList<int> l) { Spec.Requires(l != null); int s = 0; foreach (var x in l) { s = x; } return s; }
    public static void Guess(IList<int> l) { Spec.Requires(l != null); foreach (var x in l) { Spec.Assert(x == 5); } }
}");
            Assert.Empty(r.Errors("P.Has"));
            Assert.Empty(r.Errors("P.Last"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("P.Guess"));
        }
    }
}
