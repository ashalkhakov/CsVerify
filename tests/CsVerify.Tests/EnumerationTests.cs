using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// A collection changed while it is enumerated: the next MoveNext throws InvalidOperationException, and that is
    /// reported. Changing another collection, or changing this one and leaving at once, is fine; so is removing from a
    /// Dictionary (allowed since .NET Core 3.0).
    /// </summary>
    public class EnumerationTests
    {
        [Fact]
        public void ChangingACollectionInItsForeach_IsReported()
        {
            var r = Harness.Verify(@"
using System.Collections.Generic;
public static class P
{
    public static void Grow(List<int> l) { foreach (var x in l) { if (x > 0) l.Add(x); } }
    public static void Clear(List<int> l) { foreach (var x in l) { l.Clear(); } }
    public static void DictAdd(Dictionary<int, int> d) { foreach (var kv in d) { d[kv.Key + 1] = 0; } }
    public static void SetAdd(HashSet<int> s) { foreach (var x in s) { s.Add(x + 1); } }
    public static void StackPush(Stack<int> s) { foreach (var x in s) { s.Push(x); } }
    public static void Explicit(List<int> l) { var e = l.GetEnumerator(); while (e.MoveNext()) { l.Add(1); } }
}", overflow: false);
            foreach (var m in new[] { "Grow", "Clear", "DictAdd", "SetAdd", "StackPush", "Explicit" }) Assert.Equal(new[] { "CSV1001" }, r.Errors("P." + m));
        }

        [Fact]
        public void KeysAndValues_AreViewsOfTheirDictionary()
        {
            var r = Harness.Verify(@"
using System.Collections.Generic;
public static class P
{
    // a new key, or Clear: the view's next MoveNext throws
    public static void KeysAdd(Dictionary<int, int> d) { foreach (var k in d.Keys) { d[k + 1000] = 0; } }
    public static void ValuesClear(Dictionary<int, int> d) { foreach (var v in d.Values) { if (v < 0) d.Clear(); } }
    // a key's value overwritten (the version stays), or a key removed (allowed since .NET Core 3.0): fine
    public static void KeysAssign(Dictionary<string, int> d) { foreach (var k in d.Keys) { d[k] = 0; } }
    public static void PairsAssign(Dictionary<int, int> d) { foreach (var kv in d) { d[kv.Key] = 1; } }
    public static void KeysRemove(Dictionary<int, int> d) { foreach (var k in d.Keys) { d.Remove(k); } }
    // a foreach's pair is one the dictionary has; a view's Count is the dictionary's
    public static int Pair(Dictionary<int, int> d) { foreach (var kv in d) { Spec.Assert(d.ContainsKey(kv.Key) && d[kv.Key] == kv.Value); return kv.Value; } return 0; }
    public static int Count(Dictionary<int, int> d) { Spec.Ensures<int>(r => r == d.Count); return d.Keys.Count; }
}", overflow: false);
            Assert.Equal(new[] { "CSV1001" }, r.Errors("P.KeysAdd"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("P.ValuesClear"));
            foreach (var m in new[] { "KeysAssign", "PairsAssign", "KeysRemove", "Pair", "Count" }) Assert.Empty(r.Errors("P." + m));
        }

        [Fact]
        public void WhatDoesNotThrow_IsNotReported()
        {
            var r = Harness.Verify(@"
using System.Collections.Generic;
public static class P
{
    public static void Other(List<int> l, List<int> m) { Spec.Requires(l != m); foreach (var x in l) { m.Add(x); } }
    public static void Break(List<int> l) { foreach (var x in l) { if (x > 0) { l.Add(x); break; } } }
    public static int Read(List<int> l) { int s = 0; foreach (var x in l) s = x; return s; }
    public static void DictRemove(Dictionary<int, int> d) { foreach (var kv in d) { if (kv.Value < 0) d.Remove(kv.Key); } }
    // (m may be l: it may change the list being enumerated)
    public static void MaybeSame(List<int> l, List<int> m) { foreach (var x in l) { m.Add(x); } }
}", overflow: false);
            foreach (var m in new[] { "Other", "Break", "Read", "DictRemove" }) Assert.Empty(r.Errors("P." + m));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("P.MaybeSame"));
        }

        // (through an enumerator, Spec.Index counts the elements gone through; an unchanged collection gives its Count)
        [Fact]
        public void ThroughAnEnumerator_TheIndexCounts()
        {
            var r = Harness.Verify(@"
using System.Collections.Generic;
public static class P
{
    public static int Count(Dictionary<int, int> d) { Spec.Requires(d != null); Spec.Ensures((int r) => r == d.Count); int n = 0; foreach (var kv in d) { Spec.Invariant(n == Spec.Index(kv)); n = n + 1; } return n; }
    public static int Members(HashSet<int> s) { Spec.Requires(s != null); Spec.Ensures((int r) => r == s.Count); int n = 0; foreach (var x in s) { Spec.Invariant(n == Spec.Index(x)); n = n + 1; } return n; }
    public static int Off(Dictionary<int, int> d) { Spec.Requires(d != null); Spec.Ensures((int r) => r == d.Count + 1); int n = 0; foreach (var kv in d) { Spec.Invariant(n == Spec.Index(kv)); n = n + 1; } return n; }
    // (a Remove goes on while it's enumerated: then fewer than the Count it began with may be given)
    public static int Removes(Dictionary<int, int> d) { Spec.Requires(d != null); Spec.Modifies(ObjSet.Of(d)); Spec.Ensures((int r) => r == Spec.Old(d.Count));
        int n = 0; foreach (var kv in d) { Spec.Invariant(n == Spec.Index(kv)); d.Remove(kv.Key); n = n + 1; } return n; }
}");
            Assert.Empty(r.Errors("P.Count"));
            Assert.Empty(r.Errors("P.Members"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("P.Off"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("P.Removes"));
        }
    }
}
