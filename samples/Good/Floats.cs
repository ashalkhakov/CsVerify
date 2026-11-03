using System;
using CsVerify;

namespace Samples
{
    // float and double exactly as IEEE 754: rounding to nearest, NaN, the infinities and -0.0 included. What
    // verifies holds of the program as it runs. Geometry like a BVH's bounding boxes needs mostly comparisons,
    // min and max, which are exact; arithmetic rounds, and the specifications say so.

    /// <summary>An axis-aligned interval, as a bounding box has one per axis. Valid: no NaN, lo below hi.</summary>
    public sealed record Span1(float Lo, float Hi);

    public static class FloatSamples
    {
        [Pure]
        public static bool Valid(Span1 s) => !float.IsNaN(s.Lo) && !float.IsNaN(s.Hi) && s.Lo <= s.Hi;

        /// <summary>The smallest interval holding both: min and max are exact, so it does hold them.</summary>
        public static Span1 Union(Span1 a, Span1 b)
        {
            Spec.Requires(Valid(a) && Valid(b));
            Spec.Ensures((Span1 r) => Valid(r) && r.Lo <= a.Lo && r.Lo <= b.Lo && a.Hi <= r.Hi && b.Hi <= r.Hi);
            return new Span1(MathF.Min(a.Lo, b.Lo), MathF.Max(a.Hi, b.Hi));
        }

        /// <summary>Do two intervals overlap (touching counts)?</summary>
        public static bool Overlaps(Span1 a, Span1 b)
        {
            Spec.Requires(Valid(a) && Valid(b));
            Spec.Ensures((bool r) => r == (a.Lo <= b.Hi && b.Lo <= a.Hi));
            return a.Lo <= b.Hi && b.Lo <= a.Hi;
        }

        /// <summary>A box built by growing over points holds every point (the BVH build's bounds loop).</summary>
        public static Span1 Bounds(float[] xs)
        {
            Spec.Requires(xs.Length > 0 && Spec.Forall(0, xs.Length, i => !float.IsNaN(xs[i])));
            Spec.Ensures((Span1 r) => Valid(r) && Spec.Forall(0, xs.Length, i => r.Lo <= xs[i] && xs[i] <= r.Hi));
            float lo = xs[0], hi = xs[0];
            for (int i = 1; i < xs.Length; i++)
            {
                Spec.Invariant(1 <= i && i <= xs.Length && !float.IsNaN(lo) && !float.IsNaN(hi) && lo <= hi);
                Spec.Invariant(Spec.Forall(0, i, j => lo <= xs[j] && xs[j] <= hi));
                Spec.Decreases(xs.Length - i);
                lo = MathF.Min(lo, xs[i]);
                hi = MathF.Max(hi, xs[i]);
            }
            return new Span1(lo, hi);
        }

        /// <summary>The cell a coordinate falls in, on a 16-cell grid with unit cells: a float-to-int cast that fits.</summary>
        public static int Cell(float x)
        {
            Spec.Requires(0 <= x && x < 16);
            Spec.Ensures((int r) => 0 <= r && r < 16);
            return (int)x;
        }

        /// <summary>Which side of a split plane a box lies on (the BVH traversal's test): comparisons only, exact.</summary>
        public static int Side(Span1 box, float plane)
        {
            Spec.Requires(Valid(box) && !float.IsNaN(plane));
            Spec.Ensures((int r) => r == -1 ? box.Hi < plane : r == 1 ? plane < box.Lo : box.Lo <= plane && plane <= box.Hi);
            if (box.Hi < plane) return -1;
            if (plane < box.Lo) return 1;
            return 0;
        }

        /// <summary>What IEEE says, and reals would not: 0.1 + 0.2 is not 0.3, 1/0 is infinite, NaN is not itself.</summary>
        public static void Facts()
        {
            Spec.Assert(0.1 + 0.2 != 0.3);
            Spec.Assert(1.0 / 0.0 == double.PositiveInfinity);
            double nan = 0.0 / 0.0;
            Spec.Assert(nan != nan && double.IsNaN(nan));
            Spec.Assert(-0.0 == 0.0 && double.IsNaN(Math.Max(1.0, nan)));
        }
    }
}
