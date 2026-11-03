using System.Diagnostics;
using CsVerify;

namespace Samples.Buggy
{
    /// <summary>Proofs that would be unsound if accepted: non-terminating, impure, or aliasing a linear view.</summary>
    public static class ProofBugs
    {
        // CSV1011: circular "induction" without a measure would prove anything, here false.
        [Lemma, Conditional(Spec.Symbol)]
        public static void Circular(int n)
        {
            Spec.Ensures(n != n);
            Circular(n);
        }

        // CSV1011: a definition that is not a function (f(x) = f(x) + 1 has no solution).
        [Pure]
        public static int Inconsistent(int x) => Inconsistent(x) + 1;

        // CSV0013 (analyzer): a lemma is erased from the program, so its write to the array would vanish at run time.
        [Lemma, Conditional(Spec.Symbol)]
        public static void Meddling(int[] a)
        {
            Spec.Requires(a.Length > 0);
            a[0] = 0;
        }

        public static void IncrementBoth(ref PointsTo<int> a, ref PointsTo<int> b, Ptr<int> p, Ptr<int> q)
        {
            Spec.Requires(a.Addr == p.Addr && b.Addr == q.Addr && a.Value.Value < 1000 && b.Value.Value < 1000);
            Spec.Ensures(a.Value.Value == Spec.Old(a).Value.Value + 1 && b.Value.Value == Spec.Old(b).Value.Value + 1);
            Spec.Ensures(a.Addr == Spec.Old(a).Addr && b.Addr == Spec.Old(b).Addr);
            Mem.Write(ref a, p, Mem.Read(in a, p) + 1);
            Mem.Write(ref b, q, Mem.Read(in b, q) + 1);
        }

        // CSV0007 (analyzer): one view passed as two. The contract says +1, the cell gets +2.
        public static int Aliased()
        {
            var p = Mem.Alloc(0, out var v);
            IncrementBoth(ref v, ref v, p, p);
            int r = Mem.Read(in v, p);
            Mem.Free(v, p);
            return r;
        }
    }
}
