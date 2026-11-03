namespace CsVerify
{
    using System.Diagnostics;

    /// <summary>
    /// Facts of IEEE 754 arithmetic that the solver decides only slowly (by bit-blasting whole multipliers), as
    /// trusted lemmas: call one where a proof needs it. Each is the monotonicity of a correctly rounded operation
    /// (rounding to nearest preserves order), stated with exactly the hypotheses under which it holds: finite
    /// operands (an infinity times zero, or two opposite infinities added, give NaN).
    /// </summary>
    public static class Ieee
    {
        /// <summary>x ≤ y and z ≥ 0 (all finite): x·z ≤ y·z.</summary>
        [Lemma, Trusted, Conditional(Spec.Symbol)]
        public static void MulMonotone(float x, float y, float z)
        {
            Spec.Requires(x <= y && z >= 0 && float.IsFinite(x) && float.IsFinite(y) && float.IsFinite(z));
            Spec.Ensures(x * z <= y * z);
        }

        /// <summary>x ≤ y (all finite): x + z ≤ y + z.</summary>
        [Lemma, Trusted, Conditional(Spec.Symbol)]
        public static void AddMonotone(float x, float y, float z)
        {
            Spec.Requires(x <= y && float.IsFinite(x) && float.IsFinite(y) && float.IsFinite(z));
            Spec.Ensures(x + z <= y + z);
        }

        /// <summary>x ≤ y (all finite): x − z ≤ y − z.</summary>
        [Lemma, Trusted, Conditional(Spec.Symbol)]
        public static void SubMonotone(float x, float y, float z)
        {
            Spec.Requires(x <= y && float.IsFinite(x) && float.IsFinite(y) && float.IsFinite(z));
            Spec.Ensures(x - z <= y - z);
        }

        /// <summary>x ≤ y and z &gt; 0 (all finite): x / z ≤ y / z.</summary>
        [Lemma, Trusted, Conditional(Spec.Symbol)]
        public static void DivMonotone(float x, float y, float z)
        {
            Spec.Requires(x <= y && z > 0 && float.IsFinite(x) && float.IsFinite(y) && float.IsFinite(z));
            Spec.Ensures(x / z <= y / z);
        }

        /// <summary>0 ≤ x ≤ y: √x ≤ √y.</summary>
        [Lemma, Trusted, Conditional(Spec.Symbol)]
        public static void SqrtMonotone(float x, float y)
        {
            Spec.Requires(0 <= x && x <= y && !float.IsNaN(y));
            Spec.Ensures(System.MathF.Sqrt(x) <= System.MathF.Sqrt(y));
        }

        /// <summary>x ≤ y and z ≥ 0 (all finite): x·z ≤ y·z.</summary>
        [Lemma, Trusted, Conditional(Spec.Symbol)]
        public static void MulMonotone(double x, double y, double z)
        {
            Spec.Requires(x <= y && z >= 0 && double.IsFinite(x) && double.IsFinite(y) && double.IsFinite(z));
            Spec.Ensures(x * z <= y * z);
        }

        /// <summary>x ≤ y (all finite): x + z ≤ y + z.</summary>
        [Lemma, Trusted, Conditional(Spec.Symbol)]
        public static void AddMonotone(double x, double y, double z)
        {
            Spec.Requires(x <= y && double.IsFinite(x) && double.IsFinite(y) && double.IsFinite(z));
            Spec.Ensures(x + z <= y + z);
        }

        /// <summary>x ≤ y (all finite): x − z ≤ y − z.</summary>
        [Lemma, Trusted, Conditional(Spec.Symbol)]
        public static void SubMonotone(double x, double y, double z)
        {
            Spec.Requires(x <= y && double.IsFinite(x) && double.IsFinite(y) && double.IsFinite(z));
            Spec.Ensures(x - z <= y - z);
        }

        /// <summary>x ≤ y and z &gt; 0 (all finite): x / z ≤ y / z.</summary>
        [Lemma, Trusted, Conditional(Spec.Symbol)]
        public static void DivMonotone(double x, double y, double z)
        {
            Spec.Requires(x <= y && z > 0 && double.IsFinite(x) && double.IsFinite(y) && double.IsFinite(z));
            Spec.Ensures(x / z <= y / z);
        }

        /// <summary>0 ≤ x ≤ y: √x ≤ √y.</summary>
        [Lemma, Trusted, Conditional(Spec.Symbol)]
        public static void SqrtMonotone(double x, double y)
        {
            Spec.Requires(0 <= x && x <= y && !double.IsNaN(y));
            Spec.Ensures(System.Math.Sqrt(x) <= System.Math.Sqrt(y));
        }
    }
}
