using System.Diagnostics;
using CsVerify;

namespace Samples
{
    /// <summary>
    /// Ports of the classic programs-with-proofs from Hongwei Xi's "Introduction to Programming in ATS"
    /// (ats-lang.github.io, INT2PROGINATS: fact/FACT, fib/FIB, imul/MUL) and of the Euclid example. Written afresh
    /// in C#, not copied.
    ///
    /// ATS states these with a dataprop (FACT(n, r): r is n!) and returns the proof alongside the value:
    /// <c>fun fact {n:nat} (x: int n): [r:int] (FACT(n, r) | int r)</c>. CsVerify has no dataprops; the relation
    /// becomes a [Pure] function whose definition plays the role of the dataprop's constructors, and the returned
    /// proof becomes a postcondition.
    /// </summary>
    public static class AtsIntro
    {
        // ---- factorial ----------------------------------------------------------------------------------------

        /// <summary>The FACT relation: FACTbas: FACT(0, 1); FACTind: FACT(n, r) implies FACT(n+1, (n+1) r).</summary>
        [GhostFunction]
        public static int Fact(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Decreases(n);
            return n == 0 ? 1 : n * Fact(n - 1);
        }

        /// <summary>Tail-recursive factorial as a loop; the invariant is the accumulator's FACT proof.</summary>
        public static int FactIter(int n)
        {
            Spec.Requires(0 <= n && n <= 12);
            Spec.Ensures<int>(r => r == Fact(n));
            int r = 1;
            for (int i = 1; i <= n; i++)
            {
                Spec.Invariant(1 <= i && i <= n + 1);
                Spec.Invariant(r == Fact(i - 1));
                Spec.Decreases(n + 1 - i);
                r = checked(r * i); // n <= 12 keeps it in int; checked says so at run time
            }
            return r;
        }

        // ---- Fibonacci ----------------------------------------------------------------------------------------

        /// <summary>The FIB relation: FIB(0, 0), FIB(1, 1), FIB(n, r0) and FIB(n+1, r1) give FIB(n+2, r0 + r1).</summary>
        [GhostFunction]
        public static int Fib(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Decreases(n);
            return n < 2 ? n : Fib(n - 1) + Fib(n - 2);
        }

        /// <summary>The linear-time Fibonacci: two accumulators, each carrying its FIB proof.</summary>
        public static int FibIter(int n)
        {
            Spec.Requires(0 <= n && n <= 40);
            Spec.Ensures<int>(r => r == Fib(n));
            int a = 0, b = 1;
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n);
                Spec.Invariant(a == Fib(i) && b == Fib(i + 1));
                Spec.Decreases(n - i);
                int c = checked(a + b);
                a = b;
                b = c;
            }
            return a;
        }

        // ---- multiplication -----------------------------------------------------------------------------------

        /// <summary>
        /// ATS proves imul correct against the MUL dataprop (MUL(m, n, p): p = m * n) built by repeated addition.
        /// Here the relation is the solver's own multiplication; the invariant is MUL(i, y, r).
        /// </summary>
        public static int Mul(int x, int y)
        {
            Spec.Requires(x >= 0);
            Spec.Ensures<int>(r => r == x * y);
            int r = 0;
            for (int i = 0; i < x; i++)
            {
                Spec.Invariant(0 <= i && i <= x);
                Spec.Invariant(r == i * y);
                Spec.Decreases(x - i);
                r = checked(r + y);
            }
            return r;
        }

        /// <summary>
        /// The MUL lemma ATS proves by induction on m: (m+1) n = m n + n. Spelled out as a [Lemma] to show the shape
        /// of an inductive proof function; Z3 knows this one, so Mul above does not need to call it.
        /// </summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void MulSucc(int m, int n)
        {
            Spec.Requires(m >= 0);
            Spec.Ensures((m + 1) * n == m * n + n);
            Spec.Decreases(m);
            if (m > 0) MulSucc(m - 1, n);
        }

        // ---- greatest common divisor --------------------------------------------------------------------------

        /// <summary>The GCD relation, by Euclid: gcd(a, 0) = a, gcd(a, b) = gcd(b, a mod b).</summary>
        [Pure]
        public static int Gcd(int a, int b)
        {
            Spec.Requires(a >= 0 && b >= 0);
            Spec.Decreases(b);
            return b == 0 ? a : Gcd(b, a % b);
        }

        /// <summary>Euclid's loop. The invariant says the pair changes, its gcd does not.</summary>
        public static int GcdIter(int a, int b)
        {
            Spec.Requires(a >= 0 && b >= 0);
            Spec.Ensures<int>(r => r == Gcd(a, b));
            int x = a, y = b;
            while (y != 0)
            {
                Spec.Invariant(x >= 0 && y >= 0);
                Spec.Invariant(Gcd(x, y) == Gcd(a, b));
                Spec.Decreases(y);
                int t = x % y;
                x = y;
                y = t;
            }
            return x;
        }

        // ---- swap, from "Safe Programming with Pointers through Stateful Views" (Zhu and Xi, PADL 2005) -------

        /// <summary>
        /// <c>fn swap {a:t@ype} {l1,l2:addr} (pf1: !a @ l1, pf2: !a @ l2 | p1: ptr l1, p2: ptr l2): void</c>.
        /// The two views are borrowed (<c>!</c>, here <c>ref</c>) and handed back with the contents exchanged.
        /// </summary>
        public static void Swap(ref PointsTo<int> v1, ref PointsTo<int> v2, Ptr<int> p1, Ptr<int> p2)
        {
            Spec.Requires(v1.Addr == p1.Addr && v2.Addr == p2.Addr);
            Spec.Ensures(v1.Addr == Spec.Old(v1).Addr && v2.Addr == Spec.Old(v2).Addr);
            Spec.Ensures(v1.Value == Spec.Old(v2).Value && v2.Value == Spec.Old(v1).Value);
            int x = Mem.Read(in v1, p1);
            int y = Mem.Read(in v2, p2);
            Mem.Write(ref v1, p1, y);
            Mem.Write(ref v2, p2, x);
        }

        public static int SwapDemo()
        {
            Spec.Ensures<int>(r => r == 2 * 10 + 1);
            var p = Mem.Alloc(1, out var v);
            var q = Mem.Alloc(2, out var w);
            Swap(ref v, ref w, p, q);
            int r = 10 * Mem.Read(in v, p) + Mem.Read(in w, q);
            Mem.Free(v, p);
            Mem.Free(w, q);
            return r;
        }
        // ---- termination metrics (INT2PROGINATS, chapter on dependent types: acker, isevn/isodd) ---------------

        /// <summary>
        /// Ackermann's function. ATS: <c>fun acker {m,n:nat} .&lt;m, n&gt;. (x: int m, y: int n): Nat</c>. No single
        /// integer measure works; the pair (m, n) goes down lexicographically on every call: the inner call keeps m
        /// and lowers n, the other two lower m (and may raise n arbitrarily).
        /// </summary>
        public static int Ackermann(int m, int n)
        {
            Spec.Requires(m >= 0 && n >= 0);
            Spec.Ensures<int>(r => r > n);
            Spec.Decreases(m, n);
            if (m == 0) return checked(n + 1);
            if (n == 0) return Ackermann(m - 1, 1);
            return Ackermann(m - 1, Ackermann(m, n - 1));
        }

        /// <summary>
        /// Mutual recursion: <c>fun isevn {n:nat} .&lt;2*n&gt;. ... and isodd {n:nat} .&lt;2*n+1&gt;. ...</c>. isodd(n) calls
        /// isevn(n) with the same argument, so the metrics must tell the two functions apart: 2n &lt; 2n + 1.
        /// </summary>
        public static bool IsEven(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Ensures<bool>(r => r == (n % 2 == 0));
            Spec.Decreases(2 * n);
            if (n == 0) return true;
            return IsOdd(n - 1);
        }

        public static bool IsOdd(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Ensures<bool>(r => r == (n % 2 == 1));
            Spec.Decreases(2 * n + 1);
            return !IsEven(n);
        }
    }
}
