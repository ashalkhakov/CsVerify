#nullable enable
namespace CsVerify
{
    using System;
    using System.Collections;
    using System.Collections.Generic;
    using System.Linq;

    /// <summary>
    /// Comprehensions, what LINQ's meaning is written in ([Comprehensions] stubs, Bcl/Linq.cs), after Cheney, Lindley
    /// and Wadler's "A Practical Theory of Language-Integrated Query" (ICFP 2013): <c>For(s, x => body)</c> is the
    /// bodies' sequences for each x of s, one after another; <c>If(c, q)</c> is q where c holds and nothing otherwise;
    /// <c>Yield(v)</c> is v alone. A comprehension is read in order (as LINQ to Objects runs it), so
    /// <c>Q.For(s, x => Q.If(p(x), Q.Yield(x)))</c> is s's elements that p holds of, in order. Besides these:
    /// sequences' lengths and elements (<see cref="Count"/>, <see cref="At"/>), ranges of indices, folds, stable sorts
    /// and groups. These run (written without System.Linq, so that running them tests the stubs against LINQ); the
    /// verifier reads them instead.
    /// </summary>
    public static class Q
    {
        /// <summary>For each element x of the source, in order: the body's sequence for x.</summary>
        public static IEnumerable<R> For<T, R>(IEnumerable<T> source, Func<T, IEnumerable<R>> body)
        {
            var r = new List<R>();
            foreach (var x in source) foreach (var y in body(x)) r.Add(y);
            return r;
        }

        /// <summary>The sequence where the condition holds, else nothing.</summary>
        public static IEnumerable<T> If<T>(bool condition, IEnumerable<T> then) => condition ? then : new List<T>();

        /// <summary>The one value.</summary>
        public static IEnumerable<T> Yield<T>(T value) => new List<T> { value };

        /// <summary>Nothing.</summary>
        public static IEnumerable<T> Empty<T>() => new List<T>();

        /// <summary>from, from + 1, ..., to - 1 (nothing if to &lt;= from).</summary>
        public static IEnumerable<int> Range(int from, int to)
        {
            var r = new List<int>();
            for (int i = from; i < to; i++) r.Add(i);
            return r;
        }

        /// <summary>How many elements the sequence has.</summary>
        public static int Count<T>(IEnumerable<T> source)
        {
            int n = 0;
            foreach (var _ in source) n++;
            return n;
        }

        /// <summary>The element at an index (0 &lt;= index &lt; Count).</summary>
        public static T At<T>(IEnumerable<T> source, int index)
        {
            int i = 0;
            foreach (var x in source)
            {
                if (i == index) return x;
                i++;
            }
            throw new ArgumentOutOfRangeException(nameof(index));
        }

        /// <summary>The seed, stepped by each element in order.</summary>
        public static A Fold<T, A>(IEnumerable<T> source, A seed, Func<A, T, A> step)
        {
            var a = seed;
            foreach (var x in source) a = step(a, x);
            return a;
        }

        /// <summary>The fold's values after each element: as many as the source has.</summary>
        public static IEnumerable<A> Scan<T, A>(IEnumerable<T> source, A seed, Func<A, T, A> step)
        {
            var r = new List<A>();
            var a = seed;
            foreach (var x in source)
            {
                a = step(a, x);
                r.Add(a);
            }
            return r;
        }

        /// <summary>The source in its key's order (Comparer&lt;K&gt;.Default), stable: equal keys keep their order.</summary>
        public static IOrderedEnumerable<T> Sort<T, K>(IEnumerable<T> source, Func<T, K> key, bool descending) =>
            new Sorted<T>(source, new List<Comparison<T>> { By(key, descending) });

        /// <summary>A sort with one more key, ordering what its keys so far leave equal.</summary>
        public static IOrderedEnumerable<T> ThenSort<T, K>(IOrderedEnumerable<T> source, Func<T, K> key, bool descending) =>
            source is Sorted<T> s ? new Sorted<T>(s.Source, new List<Comparison<T>>(s.Keys) { By(key, descending) })
                                  : throw new ArgumentException("not a Q.Sort", nameof(source));

        /// <summary>A group: its key and its elements, which are what the function gives for the key.</summary>
        public static IGrouping<K, T> Group<K, T>(K key, Func<K, IEnumerable<T>> elementsOf) => new Grouping<K, T>(key, elementsOf(key));

        private static Comparison<T> By<T, K>(Func<T, K> key, bool descending)
        {
            var c = Comparer<K>.Default;
            return descending ? (a, b) => c.Compare(key(b), key(a)) : (a, b) => c.Compare(key(a), key(b));
        }

        private sealed class Sorted<T> : IOrderedEnumerable<T>
        {
            public readonly IEnumerable<T> Source;
            public readonly List<Comparison<T>> Keys;

            public Sorted(IEnumerable<T> source, List<Comparison<T>> keys) { Source = source; Keys = keys; }

            private int Compare(T a, T b)
            {
                foreach (var k in Keys)
                {
                    int c = k(a, b);
                    if (c != 0) return c;
                }
                return 0;
            }

            public IEnumerator<T> GetEnumerator()
            {
                // insertion sort: stable
                var r = new List<T>();
                foreach (var x in Source)
                {
                    int i = r.Count;
                    while (i > 0 && Compare(r[i - 1], x) > 0) i--;
                    r.Insert(i, x);
                }
                return r.GetEnumerator();
            }

            IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

            public IOrderedEnumerable<T> CreateOrderedEnumerable<K>(Func<T, K> keySelector, IComparer<K>? comparer, bool descending)
            {
                var c = comparer ?? Comparer<K>.Default;
                Comparison<T> by = descending ? (a, b) => c.Compare(keySelector(b), keySelector(a)) : (a, b) => c.Compare(keySelector(a), keySelector(b));
                return new Sorted<T>(Source, new List<Comparison<T>>(Keys) { by });
            }
        }

        private sealed class Grouping<K, T> : IGrouping<K, T>
        {
            private readonly IEnumerable<T> _elements;
            public Grouping(K key, IEnumerable<T> elements) { Key = key; _elements = elements; }
            public K Key { get; }
            public IEnumerator<T> GetEnumerator() => _elements.GetEnumerator();
            IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
        }
    }
}
