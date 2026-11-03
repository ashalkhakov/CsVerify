using CsVerify;

namespace Samples
{
    // Mutable static fields: fields of one object, read and written like any other heap field. A call changes the
    // ones its callee (or anything it reaches) writes, and no others.
    public static class Counter
    {
        public static int Count;
        public static int Limit = 10;
        public static int[]? Log;

        public static void Bump()
        {
            Spec.Requires(Count < int.MaxValue);
            Spec.Ensures(Count == Spec.Old(Count) + 1);
            Count++;
        }

        public static void Reset()
        {
            Spec.Ensures(Count == 0);
            Count = 0;
        }

        public static int Twice()
        {
            Spec.Requires(Count < int.MaxValue - 1);
            Spec.Ensures((int r) => r == Spec.Old(Count) + 2 && Count == r);
            int limit = Limit;
            Bump();
            Bump();
            Spec.Assert(Limit == limit); // Bump writes Count only
            return Count;
        }

        public static void Demo()
        {
            Reset();
            Bump();
            Spec.Assert(Count == 1);
            Count = 5;
            int t = Twice();
            Spec.Assert(t == 7 && Count == 7);
        }
    }
}
