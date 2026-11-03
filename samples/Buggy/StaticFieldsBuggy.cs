using CsVerify;

namespace Samples
{
    // A call that writes a static field: what the caller knew of it is gone.
    public static class CounterBuggy
    {
        public static int Count;

        public static void Bump()
        {
            Spec.Requires(Count < int.MaxValue);
            Count++;
        }

        public static void Demo()
        {
            Count = 0;
            Bump();
            Spec.Assert(Count == 1); // CSV1002: Bump promises nothing about Count
        }
    }
}
