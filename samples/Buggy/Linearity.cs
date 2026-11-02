using CsVerify;

namespace Samples.Buggy
{
    /// <summary>Linearity and ghost errors from the analyzers (downgraded to warnings for this project in .editorconfig).</summary>
    public static class Linearity
    {
        // CSV0001: the view is leaked when flag is false.
        public static void Leak(bool flag)
        {
            var p = Mem.Alloc(0, out var view);
            if (flag) Mem.Free(view, p);
        }

        // CSV0002: freed twice.
        public static void DoubleFree()
        {
            var p = Mem.Alloc(0, out var view);
            Mem.Free(view, p);
            Mem.Free(view, p);
        }

        // CSV0002: read after free.
        public static int UseAfterFree()
        {
            var p = Mem.Alloc(0, out var view);
            Mem.Free(view, p);
            return Mem.Read(in view, p);
        }

        // CSV0006: forging a view.
        public static void Forge(Ptr<int> p)
        {
            var fake = default(PointsTo<int>);
            Mem.Free(fake, p);
        }

        // CSV0010: a ghost value used at run time.
        public static int Leaky(Ghost<int> n) => n.Value;
    }
}
