using System;
using System.Diagnostics;
using CsVerify;

namespace Samples
{
    // A port of ats-miscellanea/rtrace's BVH (accs_bvh.dats; Artyom Shalkhakov, 2011): a bounding volume hierarchy
    // built by partitioning an array of primitive ids in place, then traversed, skipping subtrees whose box the
    // query misses. CsVerify has no floats, so the geometry is integral: primitives are points (P[3 id + axis]), and
    // ray tracing becomes an axis-aligned box query. What the port proves:
    //  - part: the ids are partitioned around the splitting plane, every id still a primitive's;
    //  - bvh_mk: each recursive call gets the cells of its own half of the id array (Spec.Acc ranges), so the two
    //    builds are independent; the tree has k leaves and k - 1 inner nodes, 2k - 1 in all, the bound the ATS
    //    source leaves as "TODO: prove this result"; every node's box contains its points;
    //  - split: the ATS version halves the volume while one side is empty, and "don't know if this terminates for
    //    all inputs": it does not (all points at one place). Here a split that separates nothing halves the id range
    //    instead, so building terminates (Spec.Decreases), on every input;
    //  - the query finds exactly the points a brute-force pass over the leaves finds: skipping is sound.

    /// <summary>An axis-aligned box, corners included.</summary>
    public sealed record Box(int X0, int Y0, int Z0, int X1, int Y1, int Z1);

    /// <summary>bvh_vt: a leaf (one primitive id) or a node (its box, the splitting plane, back and front subtrees).</summary>
    public abstract record Bvh
    {
        private Bvh() { }
        public sealed record Leaf(int Id) : Bvh;
        public sealed record Node(Box B, int Axis, int Dist, Bvh Back, Bvh Front) : Bvh;
    }

    public static class AtsBvh
    {
        /// <summary>Coordinates are within ±Bound, so midpoints and extents are ints.</summary>
        public const int Bound = 1000000;

        // ------------------------------------------------------------------------------------------ geometry

        [GhostFunction]
        public static bool Points(int[] p, int n) =>
            0 < n && p.Length == 3 * n && Spec.Forall(0, 3 * n, i => -Bound <= p[i] && p[i] <= Bound);

        [GhostFunction]
        public static bool InBox(int[] p, int id, Box b)
        {
            Spec.Requires(0 <= id && 3 * id + 2 < p.Length);
            return b.X0 <= p[3 * id] && p[3 * id] <= b.X1 && b.Y0 <= p[3 * id + 1] && p[3 * id + 1] <= b.Y1 &&
                   b.Z0 <= p[3 * id + 2] && p[3 * id + 2] <= b.Z1;
        }

        [GhostFunction]
        public static bool Within(Box a, Box b) =>
            b.X0 <= a.X0 && a.X1 <= b.X1 && b.Y0 <= a.Y0 && a.Y1 <= b.Y1 && b.Z0 <= a.Z0 && a.Z1 <= b.Z1;

        [Pure]
        public static bool Intersects(Box a, Box b) =>
            a.X0 <= b.X1 && b.X0 <= a.X1 && a.Y0 <= b.Y1 && b.Y0 <= a.Y1 && a.Z0 <= b.Z1 && b.Z0 <= a.Z1;

        [GhostFunction]
        public static bool Bounded(Box b) =>
            -Bound <= b.X0 && b.X0 <= Bound && -Bound <= b.X1 && b.X1 <= Bound &&
            -Bound <= b.Y0 && b.Y0 <= Bound && -Bound <= b.Y1 && b.Y1 <= Bound &&
            -Bound <= b.Z0 && b.Z0 <= Bound && -Bound <= b.Z1 && b.Z1 <= Bound;

        // ------------------------------------------------------------------------------------------ the tree's facts

        [GhostFunction]
        public static int Leaves(Bvh t)
        {
            Spec.Ensures((int r) => r >= 1);
            Spec.Decreases(t);
            return t is Bvh.Node n ? Leaves(n.Back) + Leaves(n.Front) : 1;
        }

        [GhostFunction]
        public static int Inner(Bvh t)
        {
            Spec.Decreases(t);
            return t is Bvh.Node n ? Inner(n.Back) + Inner(n.Front) + 1 : 0;
        }

        /// <summary>Every leaf is a primitive's id.</summary>
        [GhostFunction]
        public static bool Ids(Bvh t, int n)
        {
            Spec.Decreases(t);
            return t is Bvh.Node m ? Ids(m.Back, n) && Ids(m.Front, n) : t is Bvh.Leaf l && 0 <= l.Id && l.Id < n;
        }

        /// <summary>Every leaf's point is in the box.</summary>
        [GhostFunction]
        public static bool Inside(Bvh t, int[] p, int n, Box b)
        {
            Spec.Requires(3 * n <= p.Length && Ids(t, n));
            Spec.Decreases(t);
            return t is Bvh.Node m ? Inside(m.Back, p, n, b) && Inside(m.Front, p, n, b) : t is Bvh.Leaf l && InBox(p, l.Id, b);
        }

        /// <summary>Every node's box contains the points below it.</summary>
        [GhostFunction]
        public static bool WellBoxed(Bvh t, int[] p, int n)
        {
            Spec.Requires(3 * n <= p.Length && Ids(t, n));
            Spec.Decreases(t);
            return t is Bvh.Node m
                ? Inside(m.Back, p, n, m.B) && Inside(m.Front, p, n, m.B) && WellBoxed(m.Back, p, n) && WellBoxed(m.Front, p, n)
                : true;
        }

        /// <summary>The points in q, counted over every leaf (no skipping).</summary>
        [GhostFunction]
        public static int Brute(Bvh t, int[] p, int n, Box q)
        {
            Spec.Requires(3 * n <= p.Length && Ids(t, n));
            Spec.Ensures((int r) => 0 <= r && r <= Leaves(t));
            Spec.Decreases(t);
            return t is Bvh.Node m ? Brute(m.Back, p, n, q) + Brute(m.Front, p, n, q)
                 : t is Bvh.Leaf l && InBox(p, l.Id, q) ? 1 : 0;
        }

        [Lemma, Conditional(Spec.Symbol)]
        public static void Widen(Bvh t, int[] p, int n, Box a, Box b)
        {
            Spec.Requires(3 * n <= p.Length && Ids(t, n) && Inside(t, p, n, a) && Within(a, b));
            Spec.Ensures(Inside(t, p, n, b));
            Spec.Decreases(t);
            if (t is Bvh.Node m)
            {
                Widen(m.Back, p, n, a, b);
                Widen(m.Front, p, n, a, b);
            }
            else if (t is Bvh.Leaf l) Spec.Assert(InBox(p, l.Id, a) && InBox(p, l.Id, b));
        }

        /// <summary>A query that misses a box misses every point inside it: skipping the subtree loses nothing.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Miss(Bvh t, int[] p, int n, Box b, Box q)
        {
            Spec.Requires(3 * n <= p.Length && Ids(t, n) && Inside(t, p, n, b) && !Intersects(b, q));
            Spec.Ensures(Brute(t, p, n, q) == 0);
            Spec.Decreases(t);
            if (t is Bvh.Node m)
            {
                Miss(m.Back, p, n, b, q);
                Miss(m.Front, p, n, b, q);
            }
            else if (t is Bvh.Leaf l) Spec.Assert(InBox(p, l.Id, b) && !InBox(p, l.Id, q));
        }

        // ------------------------------------------------------------------------------------------ construction

        /// <summary>bbox_for_prim: the smallest box around the points of ids[lo..hi), within any box around them.</summary>
        public static Box BBoxFor(int[] ids, int lo, int hi, int[] p, int n, Box outer)
        {
            Spec.Requires(Points(p, n) && 0 <= lo && lo < hi && hi <= ids.Length && Bounded(outer));
            Spec.Requires(Spec.Forall(lo, hi, i => 0 <= ids[i] && ids[i] < n && InBox(p, ids[i], outer)));
            Spec.Ensures((Box r) => Within(r, outer) && Bounded(r) && Spec.Forall(lo, hi, i => InBox(p, ids[i], r)));
            int f = ids[lo];
            int x0 = p[3 * f], y0 = p[3 * f + 1], z0 = p[3 * f + 2];
            int x1 = x0, y1 = y0, z1 = z0;
            for (int i = lo + 1; i < hi; i++)
            {
                Spec.Invariant(lo < i && i <= hi && Within(new Box(x0, y0, z0, x1, y1, z1), outer));
                Spec.Invariant(x0 <= x1 && y0 <= y1 && z0 <= z1);
                Spec.Invariant(Spec.Forall(lo, i, j => InBox(p, ids[j], new Box(x0, y0, z0, x1, y1, z1))));
                int id = ids[i];
                x0 = Math.Min(x0, p[3 * id]); x1 = Math.Max(x1, p[3 * id]);
                y0 = Math.Min(y0, p[3 * id + 1]); y1 = Math.Max(y1, p[3 * id + 1]);
                z0 = Math.Min(z0, p[3 * id + 2]); z1 = Math.Max(z1, p[3 * id + 2]);
            }
            return new Box(x0, y0, z0, x1, y1, z1);
        }

        /// <summary>The point's coordinate along an axis (0, 1, 2).</summary>
        [Pure]
        public static int Coord(int[] p, int id, int axis)
        {
            Spec.Requires(0 <= id && 3 * id + 2 < p.Length && 0 <= axis && axis <= 2);
            return p[3 * id + axis];
        }

        /// <summary>
        /// part: the ids of [lo..hi) rearranged so those behind the plane (coordinate below dist) come first; returns
        /// where the ones in front begin. (One pass, in place of the ATS version's two scans.)
        /// </summary>
        public static int Part(int[] ids, int lo, int hi, int[] p, int n, Box outer, int axis, int dist)
        {
            Spec.Requires(Points(p, n) && 0 <= lo && lo < hi && hi <= ids.Length && ids != p && 0 <= axis && axis <= 2 && Spec.Acc(ids, lo, hi));
            Spec.Requires(Spec.Forall(lo, hi, i => 0 <= ids[i] && ids[i] < n && InBox(p, ids[i], outer)));
            Spec.Ensures((int mid) => lo <= mid && mid <= hi && Spec.Acc(ids, lo, hi));
            Spec.Ensures(Spec.Forall(lo, hi, i => 0 <= ids[i] && ids[i] < n && InBox(p, ids[i], outer)));
            Spec.Ensures((int mid) => Spec.Forall(lo, mid, i => Coord(p, ids[i], axis) < dist) && Spec.Forall(mid, hi, i => Coord(p, ids[i], axis) >= dist));
            int m = lo;
            for (int j = lo; j < hi; j++)
            {
                Spec.Invariant(lo <= m && m <= j && j <= hi);
                Spec.Invariant(Spec.Forall(lo, hi, i => 0 <= ids[i] && ids[i] < n && InBox(p, ids[i], outer)));
                Spec.Invariant(Spec.Forall(lo, m, i => Coord(p, ids[i], axis) < dist) && Spec.Forall(m, j, i => Coord(p, ids[i], axis) >= dist));
                if (Coord(p, ids[j], axis) < dist)
                {
                    Spec.Assert(InBox(p, ids[m], outer) && InBox(p, ids[j], outer));
                    int t = ids[m];          // array_ptr_exch
                    ids[m] = ids[j];
                    ids[j] = t;
                    m++;
                }
            }
            return m;
        }

        /// <summary>
        /// split: a plane across the box's longest axis, at its middle, and the ids partitioned by it. If that
        /// separates nothing, the id range is halved instead, so both sides are never empty.
        /// </summary>
        public static (int mid, int axis, int dist) Split(int[] ids, int lo, int hi, int[] p, int n, Box b)
        {
            Spec.Requires(Points(p, n) && 0 <= lo && lo + 1 < hi && hi <= ids.Length && ids != p && Bounded(b) && Spec.Acc(ids, lo, hi));
            Spec.Requires(Spec.Forall(lo, hi, i => 0 <= ids[i] && ids[i] < n && InBox(p, ids[i], b)));
            Spec.Ensures<(int mid, int axis, int dist)>(r => lo < r.mid && r.mid < hi && Spec.Acc(ids, lo, hi));
            Spec.Ensures(Spec.Forall(lo, hi, i => 0 <= ids[i] && ids[i] < n && InBox(p, ids[i], b)));
            int ex = b.X1 - b.X0, ey = b.Y1 - b.Y0, ez = b.Z1 - b.Z0;
            int axis = ex >= ey && ex >= ez ? 0 : ey >= ez ? 1 : 2;   // choose_plane: the longest axis
            int dist = axis == 0 ? b.X0 + ex / 2 : axis == 1 ? b.Y0 + ey / 2 : b.Z0 + ez / 2;
            int mid = Part(ids, lo, hi, p, n, b, axis, dist);
            if (mid == lo || mid == hi) mid = lo + (hi - lo) / 2;      // nothing separated: halve the range
            return (mid, axis, dist);
        }

        /// <summary>
        /// bvh_mk: the tree over ids[lo..hi), whose points are in b. Each half is built with the cells of its own half
        /// of the array only.
        /// </summary>
        public static Bvh Build(int[] ids, int lo, int hi, int[] p, int n, Box b)
        {
            Spec.Requires(Points(p, n) && 0 <= lo && lo < hi && hi <= ids.Length && ids != p && Bounded(b) && Spec.Acc(ids, lo, hi));
            Spec.Requires(Spec.Forall(lo, hi, i => 0 <= ids[i] && ids[i] < n && InBox(p, ids[i], b)));
            Spec.Ensures((Bvh r) => Spec.Acc(ids, lo, hi) && Ids(r, n) && Leaves(r) == hi - lo && Inner(r) == hi - lo - 1);
            Spec.Ensures((Bvh r) => Ids(r, n) && Inside(r, p, n, b) && WellBoxed(r, p, n));
            Spec.Ensures(Spec.Forall(lo, hi, i => 0 <= ids[i] && ids[i] < n && InBox(p, ids[i], b)));
            Spec.Decreases(hi - lo);
            if (hi - lo == 1) return new Bvh.Leaf(ids[lo]);
            var (mid, axis, dist) = Split(ids, lo, hi, p, n, b);
            var bl = BBoxFor(ids, lo, mid, p, n, b);
            var br = BBoxFor(ids, mid, hi, p, n, b);
            // each half's points are in its box, which is within b: said as each half is built, before the other
            // half's call changes the array
            var l = Build(ids, lo, mid, p, n, bl);
            Spec.Assert(Spec.Forall(lo, mid, i => 0 <= ids[i] && ids[i] < n && InBox(p, ids[i], b)));
            var r = Build(ids, mid, hi, p, n, br);
            Spec.Assert(Spec.Forall(mid, hi, i => 0 <= ids[i] && ids[i] < n && InBox(p, ids[i], b)));
            Widen(l, p, n, bl, b);
            Widen(r, p, n, br, b);
            return new Bvh.Node(b, axis, dist, l, r);
        }

        /// <summary>accs_initialize: the identity map of ids, the box around all points, and the tree.</summary>
        public static Bvh Initialize(int[] p, int n)
        {
            Spec.Requires(Points(p, n));
            Spec.Ensures((Bvh r) => Ids(r, n) && Leaves(r) == n && Inner(r) == n - 1 && WellBoxed(r, p, n));
            var ids = new int[n];
            var all = new Box(-Bound, -Bound, -Bound, Bound, Bound, Bound);
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && Spec.Forall(0, i, j => ids[j] == j && InBox(p, ids[j], all)));
                ids[i] = i;
            }
            var root = BBoxFor(ids, 0, n, p, n, all);
            return Build(ids, 0, n, p, n, root);
        }

        // ------------------------------------------------------------------------------------------ traversal

        /// <summary>
        /// ray_test, as a box query: the points of the tree in q. A node whose box q misses is skipped; that loses
        /// nothing (Miss), so the count is what visiting every leaf would give.
        /// </summary>
        public static int Query(Bvh t, int[] p, int n, Box q)
        {
            Spec.Requires(3 * n <= p.Length && Ids(t, n) && WellBoxed(t, p, n) && Leaves(t) < int.MaxValue);
            Spec.Ensures((int r) => r == Brute(t, p, n, q) && 0 <= r && r <= Leaves(t));
            Spec.Decreases(t);
            if (t is Bvh.Leaf l) return InBox2(p, l.Id, q) ? 1 : 0;
            var m = (Bvh.Node)t;
            if (!Intersects(m.B, q))
            {
                Miss(m.Back, p, n, m.B, q);
                Miss(m.Front, p, n, m.B, q);
                return 0;
            }
            Spec.Assert(Leaves(m.Back) >= 1 && Leaves(m.Front) >= 1); // (each side has a leaf, so each is smaller)
            return Query(m.Back, p, n, q) + Query(m.Front, p, n, q);
        }

        /// <summary>InBox, computed.</summary>
        private static bool InBox2(int[] p, int id, Box b)
        {
            Spec.Requires(0 <= id && 3 * id + 2 < p.Length);
            Spec.Ensures((bool r) => r == InBox(p, id, b));
            return b.X0 <= p[3 * id] && p[3 * id] <= b.X1 && b.Y0 <= p[3 * id + 1] && p[3 * id + 1] <= b.Y1 &&
                   b.Z0 <= p[3 * id + 2] && p[3 * id + 2] <= b.Z1;
        }

        /// <summary>Four points, two of them at the same place (which the ATS split would never separate).</summary>
        public static int Demo()
        {
            Spec.Ensures((int r) => 0 <= r && r <= 4);
            var p = new[] { 0, 0, 0, 5, 5, 5, 5, 5, 5, -3, 2, 7 };
            Spec.Assert(Points(p, 4));
            var bvh = Initialize(p, 4);
            return Query(bvh, p, 4, new Box(1, 1, 1, 9, 9, 9));
        }
    }
}
