#nullable enable
namespace CsVerify.Bcl
{
    using System;
    using System.Collections.Generic;
    using System.Linq;

    /// <summary>
    /// LINQ to Objects (System.Linq.Enumerable), member by member, as comprehensions (<see cref="Q"/>): what each
    /// gives, in order, and where it throws (its Spec.Requires). A member returning a sequence is a query, read when
    /// it is enumerated; the others are read at the call. Each definition is run against the member it defines
    /// (QueryConformanceTests). Sums are computed with long, and spec arithmetic is mathematical: Sum's precondition
    /// is that every partial sum is in range, as .NET adds them checked.
    /// </summary>
    [ContractsFor(typeof(Enumerable)), Comprehensions]
    public static class EnumerableQueries
    {
        // ------------------------------------------------------------------ queries

        public static IEnumerable<R> Select<T, R>(IEnumerable<T> source, Func<T, R> selector) =>
            Q.For(source, x => Q.Yield(selector(x)));

        public static IEnumerable<R> Select<T, R>(IEnumerable<T> source, Func<T, int, R> selector) =>
            Q.For(Q.Range(0, Q.Count(source)), i => Q.Yield(selector(Q.At(source, i), i)));

        public static IEnumerable<T> Where<T>(IEnumerable<T> source, Func<T, bool> predicate) =>
            Q.For(source, x => Q.If(predicate(x), Q.Yield(x)));

        public static IEnumerable<T> Take<T>(IEnumerable<T> source, int count) =>
            Q.For(Q.Range(0, Math.Min(Math.Max(count, 0), Q.Count(source))), i => Q.Yield(Q.At(source, i)));

        public static IEnumerable<T> Skip<T>(IEnumerable<T> source, int count) =>
            Q.For(Q.Range(Math.Min(Math.Max(count, 0), Q.Count(source)), Q.Count(source)), i => Q.Yield(Q.At(source, i)));

        // the first occurrence of each value (EqualityComparer<T>.Default), in order
        public static IEnumerable<T> Distinct<T>(IEnumerable<T> source) =>
            Q.For(Q.Range(0, Q.Count(source)), j => Q.If(Q.Unseen(source, j), Q.Yield(Q.At(source, j))));

        public static IOrderedEnumerable<T> OrderBy<T, K>(IEnumerable<T> source, Func<T, K> keySelector) => Q.Sort(source, keySelector, false);

        public static IOrderedEnumerable<T> OrderByDescending<T, K>(IEnumerable<T> source, Func<T, K> keySelector) => Q.Sort(source, keySelector, true);

        public static IOrderedEnumerable<T> ThenBy<T, K>(IOrderedEnumerable<T> source, Func<T, K> keySelector) => Q.ThenSort(source, keySelector, false);

        public static IOrderedEnumerable<T> ThenByDescending<T, K>(IOrderedEnumerable<T> source, Func<T, K> keySelector) => Q.ThenSort(source, keySelector, true);

        public static IEnumerable<R> SelectMany<T, R>(IEnumerable<T> source, Func<T, IEnumerable<R>> selector) =>
            Q.For(source, x => Q.For(selector(x), y => Q.Yield(y)));

        // the groups in the order their keys first appear, each with the source's elements of its key, in order
        public static IEnumerable<IGrouping<K, T>> GroupBy<T, K>(IEnumerable<T> source, Func<T, K> keySelector)
        {
            var keys = Select(source, keySelector);
            return Q.For(Q.Range(0, Q.Count(keys)), j => Q.If(Q.Unseen(keys, j),
                Q.Yield(Q.Group(Q.At(keys, j), k => Q.For(source, x => Q.If(Spec.Equal(Ghost.Of(keySelector(x)), Ghost.Of(k)), Q.Yield(x)))))));
        }

        // (query syntax: a second from)
        public static IEnumerable<R> SelectMany<T, C, R>(IEnumerable<T> source, Func<T, IEnumerable<C>> collectionSelector, Func<T, C, R> resultSelector) =>
            Q.For(source, x => Q.For(collectionSelector(x), y => Q.Yield(resultSelector(x, y))));

        // (query syntax: group e by k)
        public static IEnumerable<IGrouping<K, E>> GroupBy<T, K, E>(IEnumerable<T> source, Func<T, K> keySelector, Func<T, E> elementSelector)
        {
            var keys = Select(source, keySelector);
            return Q.For(Q.Range(0, Q.Count(keys)), j => Q.If(Q.Unseen(keys, j),
                Q.Yield(Q.Group(Q.At(keys, j), k => Q.For(source, x => Q.If(Spec.Equal(Ghost.Of(keySelector(x)), Ghost.Of(k)), Q.Yield(elementSelector(x))))))));
        }

        public static IEnumerable<R> GroupBy<T, K, R>(IEnumerable<T> source, Func<T, K> keySelector, Func<K, IEnumerable<T>, R> resultSelector) =>
            Q.For(GroupBy(source, keySelector), g => Q.Yield(resultSelector(g.Key, g)));

        public static IEnumerable<R> GroupBy<T, K, E, R>(IEnumerable<T> source, Func<T, K> keySelector, Func<T, E> elementSelector, Func<K, IEnumerable<E>, R> resultSelector) =>
            Q.For(GroupBy(source, keySelector, elementSelector), g => Q.Yield(resultSelector(g.Key, g)));

        public static IEnumerable<(A First, B Second)> Zip<A, B>(IEnumerable<A> first, IEnumerable<B> second) =>
            Q.For(Q.Range(0, Math.Min(Q.Count(first), Q.Count(second))), i => Q.Yield((Q.At(first, i), Q.At(second, i))));

        public static IEnumerable<R> Zip<A, B, R>(IEnumerable<A> first, IEnumerable<B> second, Func<A, B, R> resultSelector) =>
            Q.For(Q.Range(0, Math.Min(Q.Count(first), Q.Count(second))), i => Q.Yield(resultSelector(Q.At(first, i), Q.At(second, i))));

        // for each outer element in order, the inner ones with an equal key, in order
        public static IEnumerable<R> Join<A, B, K, R>(IEnumerable<A> outer, IEnumerable<B> inner, Func<A, K> outerKeySelector,
                                                      Func<B, K> innerKeySelector, Func<A, B, R> resultSelector) =>
            Q.For(outer, x => Q.For(inner, y => Q.If(Spec.Equal(Ghost.Of(outerKeySelector(x)), Ghost.Of(innerKeySelector(y))), Q.Yield(resultSelector(x, y)))));

        // for each outer element in order, it and the inner ones with an equal key, in order (query syntax: join ... into)
        public static IEnumerable<R> GroupJoin<A, B, K, R>(IEnumerable<A> outer, IEnumerable<B> inner, Func<A, K> outerKeySelector,
                                                           Func<B, K> innerKeySelector, Func<A, IEnumerable<B>, R> resultSelector) =>
            Q.For(outer, x => Q.Yield(resultSelector(x, Q.For(inner, y => Q.If(Spec.Equal(Ghost.Of(outerKeySelector(x)), Ghost.Of(innerKeySelector(y))), Q.Yield(y))))));

        public static IEnumerable<T> Concat<T>(IEnumerable<T> first, IEnumerable<T> second) =>
            Q.For(Q.Range(0, Q.Count(first) + Q.Count(second)), i => Q.Yield(i < Q.Count(first) ? Q.At(first, i) : Q.At(second, i - Q.Count(first))));

        public static IEnumerable<T> Reverse<T>(IEnumerable<T> source) =>
            Q.For(Q.Range(0, Q.Count(source)), i => Q.Yield(Q.At(source, Q.Count(source) - 1 - i)));

        // (an array's own overload, which a call on an array binds to)
        public static IEnumerable<T> Reverse<T>(T[] array) =>
            Q.For(Q.Range(0, Q.Count(array)), i => Q.Yield(Q.At(array, Q.Count(array) - 1 - i)));

        public static IEnumerable<T> Where<T>(IEnumerable<T> source, Func<T, int, bool> predicate) =>
            Q.For(Q.Range(0, Q.Count(source)), i => Q.If(predicate(Q.At(source, i), i), Q.Yield(Q.At(source, i))));

        public static IEnumerable<R> SelectMany<T, R>(IEnumerable<T> source, Func<T, int, IEnumerable<R>> selector) =>
            Q.For(Q.Range(0, Q.Count(source)), i => Q.For(selector(Q.At(source, i), i), y => Q.Yield(y)));

        public static IEnumerable<R> SelectMany<T, C, R>(IEnumerable<T> source, Func<T, int, IEnumerable<C>> collectionSelector, Func<T, C, R> resultSelector) =>
            Q.For(Q.Range(0, Q.Count(source)), i => Q.For(collectionSelector(Q.At(source, i), i), y => Q.Yield(resultSelector(Q.At(source, i), y))));

        public static IEnumerable<T> Append<T>(IEnumerable<T> source, T element) =>
            Q.For(Q.Range(0, Q.Count(source) + 1), i => Q.Yield(i < Q.Count(source) ? Q.At(source, i) : element));

        public static IEnumerable<T> Prepend<T>(IEnumerable<T> source, T element) =>
            Q.For(Q.Range(0, Q.Count(source) + 1), i => Q.Yield(i == 0 ? element : Q.At(source, i - 1)));

        public static IEnumerable<T?> DefaultIfEmpty<T>(IEnumerable<T> source) =>
            Q.For(Q.Range(0, Math.Max(Q.Count(source), 1)), i => Q.Yield(Q.Count(source) == 0 ? default : Q.At(source, i)));

        public static IEnumerable<T> DefaultIfEmpty<T>(IEnumerable<T> source, T defaultValue) =>
            Q.For(Q.Range(0, Math.Max(Q.Count(source), 1)), i => Q.Yield(Q.Count(source) == 0 ? defaultValue : Q.At(source, i)));

        public static IEnumerable<T> TakeLast<T>(IEnumerable<T> source, int count) =>
            Q.For(Q.Range(Q.Count(source) - Math.Min(Math.Max(count, 0), Q.Count(source)), Q.Count(source)), i => Q.Yield(Q.At(source, i)));

        public static IEnumerable<T> SkipLast<T>(IEnumerable<T> source, int count) =>
            Q.For(Q.Range(0, Q.Count(source) - Math.Min(Math.Max(count, 0), Q.Count(source))), i => Q.Yield(Q.At(source, i)));

        // the elements before the first that fails the test: those all of whose predecessors, and themselves, pass
        public static IEnumerable<T> TakeWhile<T>(IEnumerable<T> source, Func<T, bool> predicate)
        {
            var passing = Q.Scan(source, true, (ok, x) => ok && predicate(x));
            return Q.For(Q.Range(0, Q.Count(source)), i => Q.If(Q.At(passing, i), Q.Yield(Q.At(source, i))));
        }

        public static IEnumerable<T> TakeWhile<T>(IEnumerable<T> source, Func<T, int, bool> predicate)
        {
            var passing = Q.Scan(Q.Range(0, Q.Count(source)), true, (ok, j) => ok && predicate(Q.At(source, j), j));
            return Q.For(Q.Range(0, Q.Count(source)), i => Q.If(Q.At(passing, i), Q.Yield(Q.At(source, i))));
        }

        public static IEnumerable<T> SkipWhile<T>(IEnumerable<T> source, Func<T, bool> predicate)
        {
            var passing = Q.Scan(source, true, (ok, x) => ok && predicate(x));
            return Q.For(Q.Range(0, Q.Count(source)), i => Q.If(!Q.At(passing, i), Q.Yield(Q.At(source, i))));
        }

        public static IEnumerable<T> SkipWhile<T>(IEnumerable<T> source, Func<T, int, bool> predicate)
        {
            var passing = Q.Scan(Q.Range(0, Q.Count(source)), true, (ok, j) => ok && predicate(Q.At(source, j), j));
            return Q.For(Q.Range(0, Q.Count(source)), i => Q.If(!Q.At(passing, i), Q.Yield(Q.At(source, i))));
        }

        // the first element of each key, in order
        public static IEnumerable<T> DistinctBy<T, K>(IEnumerable<T> source, Func<T, K> keySelector)
        {
            var keys = Select(source, keySelector);
            return Q.For(Q.Range(0, Q.Count(source)), j => Q.If(Q.Unseen(keys, j), Q.Yield(Q.At(source, j))));
        }

        // set operations (EqualityComparer<T>.Default): each value once, in the order it first appears
        public static IEnumerable<T> Union<T>(IEnumerable<T> first, IEnumerable<T> second) => Distinct(Concat(first, second));

        public static IEnumerable<T> UnionBy<T, K>(IEnumerable<T> first, IEnumerable<T> second, Func<T, K> keySelector) =>
            DistinctBy(Concat(first, second), keySelector);

        public static IEnumerable<T> Intersect<T>(IEnumerable<T> first, IEnumerable<T> second) =>
            Q.For(Q.Range(0, Q.Count(first)), j => Q.If(Q.Unseen(first, j) && Contains(second, Q.At(first, j)), Q.Yield(Q.At(first, j))));

        public static IEnumerable<T> Except<T>(IEnumerable<T> first, IEnumerable<T> second) =>
            Q.For(Q.Range(0, Q.Count(first)), j => Q.If(Q.Unseen(first, j) && !Contains(second, Q.At(first, j)), Q.Yield(Q.At(first, j))));

        // (first's elements whose keys are among second, or not: one for each key)
        public static IEnumerable<T> IntersectBy<T, K>(IEnumerable<T> first, IEnumerable<K> second, Func<T, K> keySelector)
        {
            var keys = Select(first, keySelector);
            return Q.For(Q.Range(0, Q.Count(first)), j => Q.If(Q.Unseen(keys, j) && Contains(second, Q.At(keys, j)), Q.Yield(Q.At(first, j))));
        }

        public static IEnumerable<T> ExceptBy<T, K>(IEnumerable<T> first, IEnumerable<K> second, Func<T, K> keySelector)
        {
            var keys = Select(first, keySelector);
            return Q.For(Q.Range(0, Q.Count(first)), j => Q.If(Q.Unseen(keys, j) && !Contains(second, Q.At(keys, j)), Q.Yield(Q.At(first, j))));
        }

        // each element with its index
        public static IEnumerable<(int Index, T Item)> Index<T>(IEnumerable<T> source) =>
            Q.For(Q.Range(0, Q.Count(source)), i => Q.Yield((i, Q.At(source, i))));

        // ------------------------------------------------------------------ values

        public static int Count<T>(IEnumerable<T> source) => Q.Count(source);

        public static int Count<T>(IEnumerable<T> source, Func<T, bool> predicate) => Q.Count(Where(source, predicate));

        public static long LongCount<T>(IEnumerable<T> source) => Q.Count(source);

        public static long LongCount<T>(IEnumerable<T> source, Func<T, bool> predicate) => Q.Count(Where(source, predicate));

        public static bool Any<T>(IEnumerable<T> source) => Q.Count(source) > 0;

        public static bool Any<T>(IEnumerable<T> source, Func<T, bool> predicate) => Spec.Exists(0, Q.Count(source), i => predicate(Q.At(source, i)));

        public static bool All<T>(IEnumerable<T> source, Func<T, bool> predicate) => Spec.Forall(0, Q.Count(source), i => predicate(Q.At(source, i)));

        public static bool Contains<T>(IEnumerable<T> source, T value) => Spec.Exists(0, Q.Count(source), i => Spec.Equal(Ghost.Of(Q.At(source, i)), Ghost.Of(value)));

        public static T ElementAt<T>(IEnumerable<T> source, int index)
        {
            Spec.Requires(0 <= index && index < Q.Count(source)); // (else ArgumentOutOfRangeException)
            return Q.At(source, index);
        }

        public static T First<T>(IEnumerable<T> source)
        {
            Spec.Requires(Q.Count(source) > 0); // (else InvalidOperationException)
            return Q.At(source, 0);
        }

        public static T First<T>(IEnumerable<T> source, Func<T, bool> predicate)
        {
            Spec.Requires(Q.Count(Where(source, predicate)) > 0);
            return Q.At(Where(source, predicate), 0);
        }

        public static T Single<T>(IEnumerable<T> source)
        {
            Spec.Requires(Q.Count(source) == 1); // (else InvalidOperationException: none, or more than one)
            return Q.At(source, 0);
        }

        public static T Single<T>(IEnumerable<T> source, Func<T, bool> predicate)
        {
            Spec.Requires(Q.Count(Where(source, predicate)) == 1);
            return Q.At(Where(source, predicate), 0);
        }

        public static T? SingleOrDefault<T>(IEnumerable<T> source)
        {
            Spec.Requires(Q.Count(source) <= 1); // (more than one: InvalidOperationException)
            return Q.Count(source) == 1 ? Q.At(source, 0) : default;
        }

        public static T SingleOrDefault<T>(IEnumerable<T> source, T defaultValue)
        {
            Spec.Requires(Q.Count(source) <= 1);
            return Q.Count(source) == 1 ? Q.At(source, 0) : defaultValue;
        }

        public static T? SingleOrDefault<T>(IEnumerable<T> source, Func<T, bool> predicate)
        {
            Spec.Requires(Q.Count(Where(source, predicate)) <= 1);
            return Q.Count(Where(source, predicate)) == 1 ? Q.At(Where(source, predicate), 0) : default;
        }

        public static T SingleOrDefault<T>(IEnumerable<T> source, Func<T, bool> predicate, T defaultValue)
        {
            Spec.Requires(Q.Count(Where(source, predicate)) <= 1);
            return Q.Count(Where(source, predicate)) == 1 ? Q.At(Where(source, predicate), 0) : defaultValue;
        }

        // the same elements in the same order (EqualityComparer<T>.Default)
        public static bool SequenceEqual<T>(IEnumerable<T> first, IEnumerable<T> second) =>
            Q.Count(first) == Q.Count(second) && Spec.Forall(0, Q.Count(first), i => Spec.Equal(Ghost.Of(Q.At(first, i)), Ghost.Of(Q.At(second, i))));

        // the first element with the least (greatest) key, by Comparer<K>.Default: the first of a stable sort by it.
        // (Stronger than .NET where it is weaker: an empty source of a reference type gives null rather than throwing,
        // and null keys are passed over; the verifier orders only integer, char and enum keys, so of the others the
        // result is only some element.)
        public static T MinBy<T, K>(IEnumerable<T> source, Func<T, K> keySelector)
        {
            Spec.Requires(Q.Count(source) > 0);
            return Q.At(Q.Sort(source, keySelector, false), 0);
        }

        public static T MaxBy<T, K>(IEnumerable<T> source, Func<T, K> keySelector)
        {
            Spec.Requires(Q.Count(source) > 0);
            return Q.At(Q.Sort(source, keySelector, true), 0);
        }

        // where it throws, only: a key that is null, or the same as an earlier one's (ArgumentNullException,
        // ArgumentException); the dictionary itself is a library value
        public static Dictionary<K, T> ToDictionary<T, K>(IEnumerable<T> source, Func<T, K> keySelector) where K : notnull
        {
            Spec.Requires(Spec.Forall(0, Q.Count(source), i => keySelector(Q.At(source, i)) != null && Q.Unseen(Select(source, keySelector), i)));
            throw null!;
        }

        public static Dictionary<K, E> ToDictionary<T, K, E>(IEnumerable<T> source, Func<T, K> keySelector, Func<T, E> elementSelector) where K : notnull
        {
            Spec.Requires(Spec.Forall(0, Q.Count(source), i => keySelector(Q.At(source, i)) != null && Q.Unseen(Select(source, keySelector), i)));
            throw null!;
        }

        public static T? FirstOrDefault<T>(IEnumerable<T> source) => Q.Count(source) > 0 ? Q.At(source, 0) : default;

        public static T? FirstOrDefault<T>(IEnumerable<T> source, Func<T, bool> predicate) =>
            Q.Count(Where(source, predicate)) > 0 ? Q.At(Where(source, predicate), 0) : default;

        public static T Last<T>(IEnumerable<T> source)
        {
            Spec.Requires(Q.Count(source) > 0);
            return Q.At(source, Q.Count(source) - 1);
        }

        public static T Last<T>(IEnumerable<T> source, Func<T, bool> predicate)
        {
            Spec.Requires(Q.Count(Where(source, predicate)) > 0);
            return Q.At(Where(source, predicate), Q.Count(Where(source, predicate)) - 1);
        }

        public static T? LastOrDefault<T>(IEnumerable<T> source) => Q.Count(source) > 0 ? Q.At(source, Q.Count(source) - 1) : default;

        public static T? LastOrDefault<T>(IEnumerable<T> source, Func<T, bool> predicate) =>
            Q.Count(Where(source, predicate)) > 0 ? Q.At(Where(source, predicate), Q.Count(Where(source, predicate)) - 1) : default;

        // checked: every partial sum is in range (else OverflowException)
        public static int Sum(IEnumerable<int> source)
        {
            Spec.Requires(Spec.Forall(0, Q.Count(source), i =>
                int.MinValue <= Q.At(Q.Scan(source, 0L, (a, x) => a + x), i) && Q.At(Q.Scan(source, 0L, (a, x) => a + x), i) <= int.MaxValue));
            return (int)Q.Fold(source, 0L, (a, x) => a + x);
        }

        public static int Sum<T>(IEnumerable<T> source, Func<T, int> selector) => Sum(Select(source, selector));

        public static int Min(IEnumerable<int> source)
        {
            Spec.Requires(Q.Count(source) > 0);
            Spec.Ensures<int>(r => Spec.Forall(0, Q.Count(source), i => r <= Q.At(source, i)) && Spec.Exists(0, Q.Count(source), i => r == Q.At(source, i)));
            return Q.Fold(source, Q.At(source, 0), (a, x) => x < a ? x : a);
        }

        public static int Min<T>(IEnumerable<T> source, Func<T, int> selector) => Min(Select(source, selector));

        public static int Max(IEnumerable<int> source)
        {
            Spec.Requires(Q.Count(source) > 0);
            Spec.Ensures<int>(r => Spec.Forall(0, Q.Count(source), i => Q.At(source, i) <= r) && Spec.Exists(0, Q.Count(source), i => r == Q.At(source, i)));
            return Q.Fold(source, Q.At(source, 0), (a, x) => a < x ? x : a);
        }

        public static int Max<T>(IEnumerable<T> source, Func<T, int> selector) => Max(Select(source, selector));

        public static long Min(IEnumerable<long> source)
        {
            Spec.Requires(Q.Count(source) > 0);
            return Q.Fold(source, Q.At(source, 0), (a, x) => x < a ? x : a);
        }

        public static long Max(IEnumerable<long> source)
        {
            Spec.Requires(Q.Count(source) > 0);
            return Q.Fold(source, Q.At(source, 0), (a, x) => a < x ? x : a);
        }

        // checked: no step overflows (said of the sum before it, exact while none has)
        public static long Sum(IEnumerable<long> source)
        {
            Spec.Requires(Spec.Forall(0, Q.Count(source), i => Q.At(source, i) >= 0
                ? (i == 0 ? 0L : Q.At(Q.Scan(source, 0L, (a, x) => a + x), i - 1)) <= long.MaxValue - Q.At(source, i)
                : (i == 0 ? 0L : Q.At(Q.Scan(source, 0L, (a, x) => a + x), i - 1)) >= long.MinValue - Q.At(source, i)));
            return Q.Fold(source, 0L, (a, x) => a + x);
        }

        public static long Sum<T>(IEnumerable<T> source, Func<T, long> selector) => Sum(Select(source, selector));

        public static long Min<T>(IEnumerable<T> source, Func<T, long> selector) => Min(Select(source, selector));

        public static long Max<T>(IEnumerable<T> source, Func<T, long> selector) => Max(Select(source, selector));

        // the long sum over the count (a long sum of ints does not overflow: there are fewer than 2^31 of them)
        public static double Average(IEnumerable<int> source)
        {
            Spec.Requires(Q.Count(source) > 0); // (else InvalidOperationException)
            return (double)Q.Fold(source, 0L, (a, x) => a + x) / Q.Count(source);
        }

        public static double Average<T>(IEnumerable<T> source, Func<T, int> selector) => Average(Select(source, selector));

        // floating point: IEEE, added in order from 0.0 (rounded at each step, as .NET adds them)
        public static double Sum(IEnumerable<double> source) => Q.Fold(source, 0.0, (a, x) => a + x);

        public static double Sum<T>(IEnumerable<T> source, Func<T, double> selector) => Sum(Select(source, selector));

        // NaN if any is NaN; else the least, the first of equals (-0.0 and 0.0 are equal)
        public static double Min(IEnumerable<double> source)
        {
            Spec.Requires(Q.Count(source) > 0);
            return Q.Fold(source, Q.At(source, 0), (a, x) => double.IsNaN(a) ? a : x < a || double.IsNaN(x) ? x : a);
        }

        public static double Min<T>(IEnumerable<T> source, Func<T, double> selector) => Min(Select(source, selector));

        // NaN only if all are NaN; else the greatest of the others, the first of equals
        public static double Max(IEnumerable<double> source)
        {
            Spec.Requires(Q.Count(source) > 0);
            return Q.Fold(source, Q.At(source, 0), (a, x) => double.IsNaN(a) || x > a ? x : a);
        }

        public static double Max<T>(IEnumerable<T> source, Func<T, double> selector) => Max(Select(source, selector));

        // the sum over the count, but for the sign of a zero (.NET adds from the first element or from 0.0, by the
        // source's kind: an all -0.0 source averages to either zero)
        public static double Average(IEnumerable<double> source)
        {
            Spec.Requires(Q.Count(source) > 0);
            // (double.Equals: == but NaN equals NaN, so equal but for a zero's sign)
            Spec.Ensures<double>(r => Spec.Equal(Ghost.Of(r), Ghost.Of(Sum(source) / Q.Count(source))));
            throw null!;
        }

        public static double Average<T>(IEnumerable<T> source, Func<T, double> selector) => Average(Select(source, selector));

        // ------------------------------------------------------------------ folds

        public static T Aggregate<T>(IEnumerable<T> source, Func<T, T, T> func)
        {
            Spec.Requires(Q.Count(source) > 0); // (else InvalidOperationException)
            return Q.Fold(Skip(source, 1), Q.At(source, 0), func);
        }

        public static A Aggregate<T, A>(IEnumerable<T> source, A seed, Func<A, T, A> func) => Q.Fold(source, seed, func);

        public static R Aggregate<T, A, R>(IEnumerable<T> source, A seed, Func<A, T, A> func, Func<A, R> resultSelector) =>
            resultSelector(Q.Fold(source, seed, func));
    }

    /// <summary>List&lt;T&gt;'s predicate methods, as comprehensions over the list's elements.</summary>
    [ContractsFor(typeof(List<>)), Comprehensions]
    public static class ListQueries<T>
    {
        public static T? Find(List<T> @this, Predicate<T> match) =>
            Q.Count(Q.For(@this, x => Q.If(match(x), Q.Yield(x)))) > 0 ? Q.At(Q.For(@this, x => Q.If(match(x), Q.Yield(x))), 0) : default;

        public static int FindIndex(List<T> @this, Predicate<T> match) =>
            Q.Count(Q.For(Q.Range(0, Q.Count(@this)), i => Q.If(match(Q.At(@this, i)), Q.Yield(i)))) > 0
                ? Q.At(Q.For(Q.Range(0, Q.Count(@this)), i => Q.If(match(Q.At(@this, i)), Q.Yield(i))), 0)
                : -1;

        public static bool Exists(List<T> @this, Predicate<T> match) => Spec.Exists(0, Q.Count(@this), i => match(Q.At(@this, i)));

        public static bool TrueForAll(List<T> @this, Predicate<T> match) => Spec.Forall(0, Q.Count(@this), i => match(Q.At(@this, i)));
    }
}
