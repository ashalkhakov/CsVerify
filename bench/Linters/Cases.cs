// The linter benchmark's cases (see README.md). Each `#region case <name> bug|ok` is one case: a bug that should be
// reported, or harmless code that only looks like one. A case's name is <bug family>.<variant>:
//   Direct    the bug as the linter's documentation shows it;
//   Hidden    the same bug behind an alias, a helper, or a value that only sometimes is bad;
//   Harmless  code that matches the pattern but cannot go wrong.
// No case has specifications beyond what the code says: this is code as people write it.
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using CsVerify;

namespace Bench
{
    public enum Color { Red, Green, Blue }

    // ---- what both kinds of tool look for --------------------------------------------------------------------

    /// <summary>SharpSource SS006: throwing null throws a NullReferenceException instead.</summary>
    public static class ThrowNull
    {
        #region case ThrowNull.Direct bug
        public static void Direct() { throw null!; }
        #endregion

        #region case ThrowNull.Hidden bug
        public static void Hidden(bool b)
        {
            Exception? e = b ? new InvalidOperationException() : null;
            throw e!;
        }
        #endregion

        #region case ThrowNull.Harmless ok
        public static void Harmless(bool b)
        {
            Exception? e = null;
            if (b) e = new InvalidOperationException(); else e = new ArgumentException("b");
            throw e;
        }
        #endregion
    }

    /// <summary>SharpSource SS057: changing a collection while it is enumerated throws InvalidOperationException.</summary>
    public static class ModifiedWhileEnumerated
    {
        #region case ModifiedWhileEnumerated.Direct bug
        public static void Direct(List<int> l)
        {
            foreach (var x in l)
                if (x > 0) l.Add(x);
        }
        #endregion

        #region case ModifiedWhileEnumerated.HiddenAlias bug
        public static void HiddenAlias(List<int> l)
        {
            var same = l;
            foreach (var x in l)
                if (x > 0) same.Add(x);
        }
        #endregion

        private static void Grow(List<int> l) => l.Add(0);

        #region case ModifiedWhileEnumerated.HiddenCall bug
        public static void HiddenCall(List<int> l)
        {
            foreach (var x in l)
                if (x > 0) Grow(l);
        }
        #endregion

        #region case ModifiedWhileEnumerated.Harmless ok
        public static void Harmless(List<int> l)
        {
            // (the change is the last thing the loop does: the enumerator never moves again)
            foreach (var x in l)
                if (x > 0) { l.Add(x); break; }
        }
        #endregion
    }

    /// <summary>Meziantou MA0134 (and the compiler's CS4014): a task that is never awaited, so its failure is lost.</summary>
    public static class Unobserved
    {
        private static async Task Work() => await Task.Yield();

        #region case Unobserved.Direct bug
        public static async Task Direct()
        {
            Work();
            await Task.Yield();
        }
        #endregion

        #region case Unobserved.Hidden bug
        public static async Task Hidden()
        {
            var t = Work();
            await Task.Yield();
        }
        #endregion

        #region case Unobserved.Harmless ok
        public static async Task Harmless()
        {
            var t = Work();
            await Task.Yield();
            await t;
        }
        #endregion
    }

    /// <summary>A disposable that is not disposed on every path, or used after it is (CA2000's territory).</summary>
    public static class Disposal
    {
        #region case Disposal.LeakDirect bug
        public static int LeakDirect(string path)
        {
            var s = File.OpenRead(path);
            return s.ReadByte();
        }
        #endregion

        #region case Disposal.LeakHidden bug
        public static int LeakHidden(string path, bool quick)
        {
            var s = File.OpenRead(path);
            if (quick) return 0;
            using (s) return s.ReadByte();
        }
        #endregion

        #region case Disposal.UseAfterDispose bug
        public static int UseAfterDispose(string path)
        {
            var s = File.OpenRead(path);
            s.Dispose();
            return s.ReadByte();
        }
        #endregion

        #region case Disposal.Harmless ok
        public static int Harmless(string path)
        {
            using var s = File.OpenRead(path);
            return s.ReadByte();
        }
        #endregion
    }

    #region case DisposableField.Direct bug
    /// <summary>SharpSource SS066: a disposable field its owner never disposes, so the file stays open.</summary>
    public sealed class FieldNotDisposed : IDisposable
    {
        private readonly FileStream _stream;
        public FieldNotDisposed(string path) { _stream = File.OpenRead(path); }
        public int Next() => _stream.ReadByte();
        public void Dispose() { }
    }
    #endregion

    #region case DisposableField.Harmless ok
    public sealed class FieldDisposed : IDisposable
    {
        private readonly FileStream _stream;
        public FieldDisposed(string path) { _stream = File.OpenRead(path); }
        public int Next() => _stream.ReadByte();
        public void Dispose() => _stream.Dispose();
    }
    #endregion

    /// <summary>SharpSource SS014: a format string with more placeholders than arguments throws FormatException.</summary>
    public static class FormatArguments
    {
        private const string Pair = "{0} and {1}";

        #region case FormatArguments.Direct bug
        public static string Direct(int a) => string.Format("{0} and {1}", a);
        #endregion

        #region case FormatArguments.Hidden bug
        public static string Hidden(int a) => string.Format(Pair, a);
        #endregion

        #region case FormatArguments.Harmless ok
        public static string Harmless(int a) => string.Format("{0} and {0}", a);
        #endregion
    }

    /// <summary>SharpSource SS018 (and the compiler's CS8509): a switch expression that misses a value throws.</summary>
    public static class SwitchExpression
    {
        #region case SwitchExpression.Direct bug
        public static int Direct(Color c) => c switch { Color.Red => 1, Color.Green => 2 };
        #endregion

        #region case SwitchExpression.Hidden bug
        /// <summary>Every member is named, but an enum may hold any int: (Color)7 throws.</summary>
        public static int Hidden(Color c) => c switch { Color.Red => 1, Color.Green => 2, Color.Blue => 3 };
        #endregion

        #region case SwitchExpression.Harmless ok
        /// <summary>The value no arm matches was returned for earlier.</summary>
        public static int Harmless(int x)
        {
            if (x == 0) return 0;
            return x switch { > 0 => 1, < 0 => -1 };
        }
        #endregion
    }

    // ---- what only linters look for (CsVerify has no rule for these) ----------------------------------------

    public static class LinterOnly
    {
        #region case NaNComparison.Direct bug
        /// <summary>Meziantou MA0082: nothing equals NaN, so this is always false.</summary>
        public static bool NaNDirect(double d) => d == double.NaN;
        #endregion

        #region case NaNComparison.Harmless ok
        public static bool NaNHarmless(double d) => double.IsNaN(d);
        #endregion

        #region case UnusedResult.Direct bug
        /// <summary>SharpSource SS040: strings are immutable, so the trimmed string is lost.</summary>
        public static string UnusedResult(string s) { s.Trim(); return s; }
        #endregion

        #region case OrderByTwice.Direct bug
        /// <summary>SharpSource SS055: the second OrderBy undoes the first; ThenBy was meant.</summary>
        public static List<(int a, int b)> OrderByTwice(List<(int a, int b)> l) => l.OrderBy(p => p.a).OrderBy(p => p.b).ToList();
        #endregion

        #region case TimeSpanTicks.Direct bug
        /// <summary>SharpSource SS068: TimeSpan(long) takes ticks, so this is half a microsecond, not five seconds.</summary>
        public static TimeSpan TimeSpanTicks() => new TimeSpan(5);
        #endregion

        #region case BlockingResult.Direct bug
        /// <summary>SharpSource SS034/SS035: blocking on a task can deadlock.</summary>
        public static int BlockingResult() => Task.FromResult(1).Result;
        #endregion

        #region case IdenticalBranches.Direct bug
        /// <summary>Meziantou MA0140: both branches are the same, so the condition does nothing.</summary>
        public static int IdenticalBranches(bool b) { if (b) return 1; else return 1; }
        #endregion
    }

    // ---- what only CsVerify looks for (no linter has a rule for these) --------------------------------------

    public static class VerifierOnly
    {
        private static string? Find(int key) => key > 0 ? "found" : null;

        #region case Null.Direct bug
        public static int NullDirect(int key) => Find(key)!.Length;
        #endregion

        #region case Null.Hidden bug
        public static int NullHidden(Dictionary<int, string> names, int key)
        {
            names.TryGetValue(key, out var name);
            return name!.Length;
        }
        #endregion

        #region case Null.Harmless ok
        public static int NullHarmless(Dictionary<int, string> names, int key) =>
            names.TryGetValue(key, out var name) ? name.Length : 0;
        #endregion

        #region case Bounds.Direct bug
        public static int Last(int[] a) => a[a.Length];
        #endregion

        #region case Bounds.Hidden bug
        public static int Max(int[] a)
        {
            int s = 0;
            for (int i = 0; i <= a.Length; i++) s = Math.Max(s, a[i]);
            return s;
        }
        #endregion

        #region case Bounds.Harmless ok
        public static int MaxHarmless(int[] a)
        {
            int s = 0;
            for (int i = 0; i < a.Length; i++) s = Math.Max(s, a[i]);
            return s;
        }
        #endregion

        #region case Overflow.Direct bug
        /// <summary>The binary-search midpoint: lo + hi overflows for large indices.</summary>
        public static int Midpoint(int lo, int hi)
        {
            if (lo < 0 || hi < lo) return lo;
            return (lo + hi) / 2;
        }
        #endregion

        #region case Overflow.Harmless ok
        public static int MidpointHarmless(int lo, int hi)
        {
            if (lo < 0 || hi < lo) return lo;
            return lo + (hi - lo) / 2;
        }
        #endregion

        #region case DivideByZero.Direct bug
        public static int Share(int total, List<int> l) => total / l.Count;
        #endregion

        #region case DivideByZero.Harmless ok
        public static int ShareHarmless(int total, List<int> l) => l.Count == 0 ? 0 : total / l.Count;
        #endregion
    }
}
