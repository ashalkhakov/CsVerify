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

        public static IEnumerable<R> Zip<A, B, R>(IEnumerable<A> first, IEnumerable<B> second, Func<A, B, R> resultSelector) =>
            Q.For(Q.Range(0, Math.Min(Q.Count(first), Q.Count(second))), i => Q.Yield(resultSelector(Q.At(first, i), Q.At(second, i))));

        // for each outer element in order, the inner ones with an equal key, in order
        public static IEnumerable<R> Join<A, B, K, R>(IEnumerable<A> outer, IEnumerable<B> inner, Func<A, K> outerKeySelector,
                                                      Func<B, K> innerKeySelector, Func<A, B, R> resultSelector) =>
            Q.For(outer, x => Q.For(inner, y => Q.If(Spec.Equal(Ghost.Of(outerKeySelector(x)), Ghost.Of(innerKeySelector(y))), Q.Yield(resultSelector(x, y)))));

        // ------------------------------------------------------------------ values

        public static int Count<T>(IEnumerable<T> source) => Q.Count(source);

        public static int Count<T>(IEnumerable<T> source, Func<T, bool> predicate) => Q.Count(Where(source, predicate));

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

        // (floating point: the value is not modeled, only that an empty sequence throws)
        public static double Min(IEnumerable<double> source)
        {
            Spec.Requires(Q.Count(source) > 0);
            throw null!;
        }

        public static double Max(IEnumerable<double> source)
        {
            Spec.Requires(Q.Count(source) > 0);
            throw null!;
        }
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
