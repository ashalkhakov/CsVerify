// (a namespace of its own, the usings inside it: Samples has a List data type of its own)
namespace Samples.Library
{
    using System.Collections.Generic;
    using CsVerify;
    using CsVerify.Bcl;

    // Code over the BCL, which the program has no sources of: List<T>, Dictionary<K, V>, string and Math get their
    // contracts from CsVerify's [ContractsFor] stubs (src/CsVerify.Spec/Bcl), and a list's contents are its model
    // functions Items() and Size(). The stubs are trusted: `csverify -v` lists the ones each run assumed.
    public static class LibraryContracts
    {
        /// <summary>The first n squares, in order.</summary>
        public static List<int> Squares(int n)
        {
            Spec.Requires(0 <= n && n <= 1000);
            Spec.Modifies(ObjSet.Empty); // (only the list it makes: callers' lists keep what they hold)
            Spec.Ensures<List<int>>(r => r.Count == n);
            Spec.Ensures<List<int>>(r => Spec.Forall(0, n, i => r[i] == i * i));
            var squares = new List<int>(n);
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && squares.Count == i);
                Spec.Invariant(Spec.Forall(0, i, j => squares[j] == j * j));
                squares.Add(i * i);
            }
            return squares;
        }

        /// <summary>The largest element of a non-empty list.</summary>
        public static int Max(List<int> l)
        {
            Spec.Requires(l.Count > 0);
            Spec.Ensures<int>(r => Spec.Forall(0, l.Count, i => l[i] <= r));
            Spec.Ensures<int>(r => Spec.Exists(0, l.Count, i => l[i] == r));
            int best = l[0];
            for (int i = 1; i < l.Count; i++)
            {
                Spec.Invariant(1 <= i && i <= l.Count);
                Spec.Invariant(Spec.Forall(0, i, j => l[j] <= best));
                Spec.Invariant(Spec.Exists(0, i, j => l[j] == best));
                if (l[i] > best) best = l[i];
            }
            return best;
        }

        /// <summary>Moves the last element of one list to another: only those two change (Spec.Modifies).</summary>
        public static void MoveLast(List<int> from, List<int> to)
        {
            Spec.Requires(from != to && from.Count > 0);
            Spec.Modifies(ObjSet.Of(from).Add(to));
            Spec.Ensures(from.Count == Spec.Old(from.Count) - 1);
            Spec.Ensures(to.Count == Spec.Old(to.Count) + 1);
            Spec.Ensures(to[to.Count - 1] == Spec.Old(from[from.Count - 1]));
            int last = from[from.Count - 1];
            from.RemoveAt(from.Count - 1);
            to.Add(last);
        }

        /// <summary>Counts how often each number occurs.</summary>
        public static Dictionary<int, int> Histogram(int[] values)
        {
            Spec.Modifies(ObjSet.Empty);
            Spec.Ensures<Dictionary<int, int>>(r => Spec.Forall(0, values.Length, i => r.ContainsKey(values[i])));
            var counts = new Dictionary<int, int>();
            for (int i = 0; i < values.Length; i++)
            {
                Spec.Invariant(0 <= i && i <= values.Length);
                Spec.Invariant(Spec.Forall(0, i, j => counts.ContainsKey(values[j])));
                counts[values[i]] = counts.TryGetValue(values[i], out int c) ? unchecked(c + 1) : 1;
            }
            return counts;
        }

        /// <summary>The part of a "key=value" pair after the '='.</summary>
        public static string ValueOf(string pair)
        {
            int eq = pair.IndexOf('=');
            if (eq < 0) return "";
            return pair.Substring(eq + 1);
        }

        public static int Demo()
        {
            var a = Squares(4);
            var b = new List<int>();
            MoveLast(a, b);
            Spec.Assert(a.Count == 3 && b.Count == 1 && b[0] == 9);
            var values = new[] { 1, 2, 1 };
            var h = Histogram(values);
            Spec.Assert(h.ContainsKey(values[1]));
            return unchecked(Max(a) + b[0] + h.Count + ValueOf("k=v").Length); // 4 + 9 + 2 + 1
        }
    }
}
