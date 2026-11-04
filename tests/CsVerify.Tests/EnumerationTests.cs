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
    }
}
