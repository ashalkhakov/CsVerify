using System.Diagnostics;
using CsVerify;

namespace Samples
{
    // A port of ATS-playground's dlist (Artyom Shalkhakov, after Hongwei Xi's libats/ngc dlist): doubly-linked
    // segments seen from the front (dlfseg_v) and from the back (dlrseg_v), and the circular list dlfcircular_v: a head
    // node and a forward segment from its next back round to it.
    //
    // dlist.sats states dlfseg_lemma3 (a non-empty segment's leftmost node is not the node after its rightmost) as
    // "unproven, because to show this, we'd have to always assume and check that at-proofs don't alias (and they
    // don't!)". As stated it is false (Lemma3Counterexample: one node pointing at itself). What the walks round a
    // circular list need is true, and here it is proved from exactly that non-aliasing: the head's permission is in
    // hand, so the head is not in the segment, and a walk that is back at the head has nothing left.

    /// <summary>dlnode_vt: @{x = int, p = ptr lp, n = ptr ln}.</summary>
    [Owned]
    public sealed class CNode
    {
        public int X;
        public CNode? P, N;

        public CNode(int x)
        {
            Spec.Ensures(X == x && P == null && N == null);
            X = x;
        }
    }

    public static class AtsDList
    {
        /// <summary>dlfseg_v(n, lf, lfp, lr, lrn): n nodes from lf (whose prev is lfp) to lr (whose next is lrn).</summary>
        [Predicate]
        public static bool FSeg(int n, CNode? lf, CNode? lfp, CNode? lr, CNode? lrn) =>
            n == 0 ? lf == lrn && lfp == lr
                   : n > 0 && lf != null && Spec.Acc(lf) && lf.P == lfp && FSeg(n - 1, lf.N, lf, lr, lrn);

        /// <summary>dlrseg_v: the same segment, built from its rightmost node.</summary>
        [Predicate]
        public static bool RSeg(int n, CNode? lf, CNode? lfp, CNode? lr, CNode? lrn) =>
            n == 0 ? lf == lrn && lfp == lr
                   : n > 0 && lr != null && Spec.Acc(lr) && lr.N == lrn && RSeg(n - 1, lf, lfp, lr.P, lr);

        /// <summary>dlfcircular_v(n, l): empty (null), or a head and a forward segment from its next round to it.</summary>
        [Predicate]
        public static bool Circular(int n, CNode? head) =>
            n == 0 ? head == null
                   : n > 0 && head != null && Spec.Acc(head) && FSeg(n - 1, head.N, head, head.P, head);

        // ------------------------------------------------------------------------------------------ proofs

        /// <summary>A forward segment, then the node after it: a segment one longer.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Extend(int n, CNode? lf, CNode? lfp, CNode? lr, CNode x)
        {
            Spec.Requires(n >= 0 && FSeg(n, lf, lfp, lr, x) && Spec.Acc(x) && x.P == lr);
            Spec.Ensures(FSeg(n + 1, lf, lfp, x, x.N));
            Spec.Decreases(n);
            Spec.Unfold(FSeg(n, lf, lfp, lr, x));
            if (n == 0)
            {
                Spec.Fold(FSeg(0, x.N, x, x, x.N));
                Spec.Fold(FSeg(1, lf, lfp, x, x.N));
            }
            else
            {
                Extend(n - 1, lf!.N, lf, lr, x);
                Spec.Fold(FSeg(n + 1, lf, lfp, x, x.N));
            }
        }

        /// <summary>
        /// dlfseg_lemma3, as the walks need it: with the head's permission in hand, a segment ending at the head is
        /// empty exactly when it starts there. (Permissions do not alias: the head is not in the segment.)
        /// </summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Lemma3(int n, CNode? lf, CNode? lfp, CNode? lr, CNode head)
        {
            Spec.Requires(n >= 0 && Spec.Acc(head) && FSeg(n, lf, lfp, lr, head));
            Spec.Ensures(Spec.Acc(head) && FSeg(n, lf, lfp, lr, head) && (n == 0) == (lf == head));
            Spec.Unfold(FSeg(n, lf, lfp, lr, head));
            Spec.Fold(FSeg(n, lf, lfp, lr, head));
        }

        /// <summary>
        /// dlfseg_lemma3 as dlist.sats states it does not hold: one node pointing at itself is a segment of one whose
        /// leftmost node is the node after its rightmost.
        /// </summary>
        public static void Lemma3Counterexample()
        {
            var a = Node(1);
            a.N = a;
            a.P = a;
            Spec.Fold(FSeg(0, a.N, a, a, a));
            Spec.Fold(FSeg(1, a, a, a, a));
            Spec.Assert(FSeg(1, a, a, a, a) && a == a); // n > 0, and lf == lrn
        }

        // ------------------------------------------------------------------------------------------ circular lists

        private static CNode Node(int x)
        {
            Spec.Ensures((CNode r) => Spec.Acc(r) && r.X == x);
            var node = Own.New(new CNode(x), out var view);
            Own.ToAcc(view);
            return node;
        }

        /// <summary>A circular list of one: a node whose prev and next are itself.</summary>
        public static CNode MakeSingle(CNode e)
        {
            Spec.Requires(Spec.Acc(e));
            Spec.Ensures((CNode r) => r == e && Circular(1, r));
            e.N = e;
            e.P = e;
            Spec.Fold(FSeg(0, e.N, e, e.P, e));
            Spec.Fold(Circular(1, e));
            return e;
        }

        /// <summary>Insert a free node right after the head (from dlist.sats's wish list).</summary>
        public static void InsertAfterHead(CNode head, int n, CNode e)
        {
            Spec.Requires(n > 0 && n < int.MaxValue && Circular(n, head) && Spec.Acc(e));
            Spec.Ensures(Circular(n + 1, head));
            Spec.Unfold(Circular(n, head));
            var first = head.N;
            if (n == 1)
            {
                Spec.Unfold(FSeg(0, first, head, head.P, head)); // first is the head, and so is its prev
                e.N = head;
                e.P = head;
                head.N = e;
                head.P = e;
                Spec.Fold(FSeg(0, e.N, e, e, head));
                Spec.Fold(FSeg(1, e, head, e, head));
                Spec.Fold(Circular(2, head));
                return;
            }
            var last = head.P;
            Spec.Unfold(FSeg(n - 1, first, head, last, head));
            first!.P = e;
            Spec.Fold(FSeg(n - 1, first, e, last, head));
            e.N = first;
            e.P = head;
            Spec.Fold(FSeg(n, e, head, last, head));
            head.N = e;
            Spec.Fold(Circular(n + 1, head));
        }

        /// <summary>
        /// dlfcircular_ptr_length: from the head's next round until the head comes back. The part walked is a segment
        /// from the head's next up to the cursor, the rest one from the cursor round to the head.
        /// </summary>
        public static int Length(CNode? head, int n)
        {
            Spec.Requires(n >= 0 && Circular(n, head));
            Spec.Ensures((int r) => r == n && Circular(n, head));
            if (head == null)
            {
                Spec.Unfold(Circular(n, head));
                Spec.Fold(Circular(n, head));
                return 0;
            }
            Spec.Unfold(Circular(n, head));
            CNode? p = head.N, prev = head;
            var last = head.P;
            int k = 1;
            Spec.Fold(FSeg(0, head.N, head, prev, p));
            while (p != head)
            {
                Spec.Invariant(1 <= k && k <= n && Spec.Acc(head) && head.P == last);
                Spec.Invariant(FSeg(k - 1, head.N, head, prev, p) && FSeg(n - k, p, prev, last, head));
                Lemma3(n - k, p, prev, last, head);          // not back at the head: there is a node here
                Spec.Unfold(FSeg(n - k, p, prev, last, head));
                var cur = p!;
                var next = cur.N;
                Extend(k - 1, head.N, head, prev, cur);
                prev = cur;
                p = next;
                k++;
            }
            Lemma3(n - k, p, prev, last, head);              // back at the head: nothing left, k is n
            Spec.Unfold(FSeg(n - k, p, prev, last, head));
            Spec.Fold(Circular(n, head));
            return k;
        }

        /// <summary>dlfcircular_ptr_free: once round, letting every node go (the collector frees them).</summary>
        public static void Free(CNode? head, int n)
        {
            Spec.Requires(n >= 0 && Circular(n, head));
            if (head == null) return;
            Spec.Unfold(Circular(n, head));
            CNode? p = head.N, prev = head;
            var last = head.P;
            int k = 1;
            while (p != head)
            {
                Spec.Invariant(1 <= k && k <= n && Spec.Acc(head) && FSeg(n - k, p, prev, last, head));
                Lemma3(n - k, p, prev, last, head);
                Spec.Unfold(FSeg(n - k, p, prev, last, head));
                prev = p;
                p = p!.N;                                    // (the node just passed is let go)
                k++;
            }
            Lemma3(n - k, p, prev, last, head);
        }

        /// <summary>fprint_dlfcircular, summing the values instead of printing them.</summary>
        public static long Sum(CNode head, int n)
        {
            Spec.Requires(n > 0 && n < 1000 && Circular(n, head));
            Spec.Ensures(Circular(n, head));
            Spec.Unfold(Circular(n, head));
            long sum = head.X;
            CNode? p = head.N, prev = head;
            var last = head.P;
            int k = 1;
            Spec.Fold(FSeg(0, head.N, head, prev, p));
            while (p != head)
            {
                Spec.Invariant(1 <= k && k <= n && Spec.Acc(head) && head.P == last && -2147483648L * k <= sum && sum <= 2147483647L * k);
                Spec.Invariant(FSeg(k - 1, head.N, head, prev, p) && FSeg(n - k, p, prev, last, head));
                Lemma3(n - k, p, prev, last, head);
                Spec.Unfold(FSeg(n - k, p, prev, last, head));
                var cur = p!;
                sum += cur.X;                                // (fprint_dlnode_ptr)
                var next = cur.N;
                Extend(k - 1, head.N, head, prev, cur);
                prev = cur;
                p = next;
                k++;
            }
            Lemma3(n - k, p, prev, last, head);
            Spec.Unfold(FSeg(n - k, p, prev, last, head));
            Spec.Fold(Circular(n, head));
            return sum;
        }

        /// <summary>test-dlist: a circular list of three, its length, and freeing it.</summary>
        public static int Demo()
        {
            Spec.Ensures((int r) => r == 3);
            var head = MakeSingle(Node(1));
            InsertAfterHead(head, 1, Node(3));
            InsertAfterHead(head, 2, Node(2));
            long sum = Sum(head, 3);
            int len = Length(head, 3);
            Free(head, 3);
            return len;
        }
    }
}
