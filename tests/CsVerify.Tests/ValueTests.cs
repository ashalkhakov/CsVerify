using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// Values and equality: strings compare by contents, Spec.Equal is EqualityComparer&lt;T&gt;.Default's, map keys
    /// compare the same way, and the collections whose contracts rest on them (List, HashSet, Stack, Queue).
    /// </summary>
    public class ValueTests
    {
        [Fact]
        public void Strings_AreTheirValues()
        {
            var r = Harness.Verify(@"
#nullable enable
public static class P
{
    public static bool Length(string a, string b) { Spec.Ensures<bool>(r => !r || a.Length == b.Length); return a == b; }
    public static bool Literals() { Spec.Ensures<bool>(r => !r); return ""ab"" == ""cd""; }
    public static bool SameLiteral() { Spec.Ensures<bool>(r => r); return ""ab"" == ""ab""; }
    public static bool Equals1(string a, string b) { Spec.Ensures<bool>(r => r == (a == b)); return a.Equals(b); }
    public static bool Ordinal(string? a, string? b) { Spec.Ensures<bool>(r => r == (a == b)); return string.Equals(a, b, StringComparison.Ordinal); }
    public static int Switch(string s) { Spec.Ensures<int>(r => s != ""a"" || r == 1); return s switch { ""a"" => 1, ""b"" => 2, _ => 0 }; }
    // false claims: a new string may equal a literal; equal strings may or may not be one object
    public static bool New() { Spec.Ensures<bool>(r => !r); return new string('a', 1) == ""a""; }
    public static bool Objects(string a, string b) { Spec.Ensures<bool>(r => r == (a == b)); return (object)a == (object)b; }
}");
            foreach (var m in new[] { "Length", "Literals", "SameLiteral", "Equals1", "Ordinal", "Switch" }) Assert.Empty(r.Errors("P." + m));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("New"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Objects"));
        }

        [Fact]
        public void DictionaryKeys_CompareAsTheDictionaryDoes()
        {
            var r = Harness.Verify(@"
#nullable enable
using System.Collections.Generic;
public sealed class Key { public int V; public override bool Equals(object? o) => o is Key k && k.V == V; public override int GetHashCode() => V; }
public static class P
{
    public static bool Strings(string k1, string k2)
    {
        Spec.Requires(k1 == k2);
        Spec.Ensures<bool>(r => r);
        var d = new Dictionary<string, int>();
        d[k1] = 1;
        return d.ContainsKey(k2);
    }
    // two different Key objects may be one key (Equals says so): not known absent
    public static bool Custom(Key k1, Key k2)
    {
        Spec.Requires(k1 != k2);
        Spec.Ensures<bool>(r => !r);
        var d = new Dictionary<Key, int>();
        d[k1] = 1;
        return d.ContainsKey(k2);
    }
    public static bool SameCustom(Key k)
    {
        Spec.Ensures<bool>(r => r);
        var d = new Dictionary<Key, int>();
        d[k] = 1;
        return d.ContainsKey(k);
    }
}");
            Assert.Empty(r.Errors("Strings"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Custom"));
            Assert.Empty(r.Errors("SameCustom"));
        }

        [Fact]
        public void ListSearches_AreExact_WhereEqualityIsKnown()
        {
            var r = Harness.Verify(@"
#nullable enable
using System.Collections.Generic;
public sealed class Eq { public int V; public override bool Equals(object? o) => o is Eq e && e.V == V; public override int GetHashCode() => V; }
public static class P
{
    public static int Find(List<int> l) { Spec.Requires(l.Count == 3 && l[0] == 5 && l[1] == 7 && l[2] == 7); Spec.Ensures<int>(r => r == 1); return l.IndexOf(7); }
    public static bool Has(List<string> l) { Spec.Requires(l.Count == 1 && l[0] == ""a""); Spec.Ensures<bool>(r => r); return l.Contains(""a""); }
    public static bool Missing(List<int> l) { Spec.Requires(l.Count == 1 && l[0] == 5); Spec.Ensures<bool>(r => !r); return l.Contains(6); }
    public static void Remove(List<int> l) { Spec.Requires(l.Count == 2 && l[0] == 1 && l[1] == 2); Spec.Modifies(ObjSet.Of(l)); l.Remove(1); Spec.Assert(l.Count == 1 && l[0] == 2); }
    // Eq's Equals is its own: two different objects may be equal
    public static bool Custom(List<Eq> l, Eq e) { Spec.Requires(l.Count == 1 && l[0] != e); Spec.Ensures<bool>(r => !r); return l.Contains(e); }
}");
            foreach (var m in new[] { "Find", "Has", "Missing", "Remove" }) Assert.Empty(r.Errors("P." + m));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("P.Custom"));
        }

        [Fact]
        public void SetsStacksAndQueues_FollowTheirModels()
        {
            var r = Harness.Verify(@"
using System.Collections.Generic;
public static class P
{
    public static bool Set() { var s = new HashSet<string>(); s.Add(""a""); s.Add(""a""); Spec.Assert(s.Count == 1); return s.Contains(""a""); }
    public static bool Removed() { var s = new HashSet<int>(); s.Add(1); s.Remove(1); Spec.Assert(s.Count == 0); return !s.Contains(1); }
    public static int Stack() { var s = new Stack<int>(); s.Push(1); s.Push(2); var a = s.Pop(); Spec.Assert(a == 2 && s.Count == 1 && s.Peek() == 1); return a; }
    public static int Queue() { var q = new Queue<int>(); q.Enqueue(1); q.Enqueue(2); var a = q.Dequeue(); Spec.Assert(a == 1 && q.Count == 1 && q.Peek() == 2); return a; }
    public static int Empty() { var s = new Stack<int>(); return s.Pop(); }
}");
            foreach (var m in new[] { "Set", "Removed", "Stack", "Queue" }) Assert.Empty(r.Errors("P." + m));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("Empty"));
        }
    }
}
