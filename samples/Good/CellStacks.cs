using CsVerify;

namespace Samples
{
    // A bounded stack over an array, as a predicate holding both the object and its array's cells (ATS: a
    // viewtype whose view includes array_v). Pushing on one stack changes only its cells; another stack's cells,
    // and every other array, stay as they were.

    [Owned]
    public sealed class CellStack
    {
        public int[] Items;
        public int Count;

        public CellStack(int capacity)
        {
            Spec.Requires(capacity >= 0);
            Spec.Ensures(Items != null && Spec.Acc(Items) && Items.Length == capacity && Count == 0);
            Items = new int[capacity];
            Count = 0;
        }
    }

    public static class CellStacks
    {
        /// <summary>A stack of n items: the object, its array's cells, and a count within them.</summary>
        [Predicate]
        public static bool Stack(CellStack s, int n) =>
            Spec.Acc(s) && s.Items != null && Spec.Acc(s.Items) && s.Count == n && 0 <= n && n <= s.Items.Length;

        /// <summary>A new, empty stack.</summary>
        public static CellStack Make(int capacity)
        {
            Spec.Requires(capacity >= 0);
            Spec.Ensures((CellStack r) => Stack(r, 0));
            var s = Own.New(new CellStack(capacity), out var view);
            Own.ToAcc(view);
            Spec.Fold(Stack(s, 0));
            return s;
        }

        /// <summary>Pushes if there is room; says whether it did.</summary>
        public static bool PushItem(CellStack s, int n, int v)
        {
            Spec.Requires(Stack(s, n));
            Spec.Ensures((bool r) => r ? Stack(s, n + 1) : Stack(s, n));
            Spec.Unfold(Stack(s, n));
            if (s.Count < s.Items.Length)
            {
                s.Items[s.Count] = v;
                s.Count++;
                Spec.Fold(Stack(s, n + 1));
                return true;
            }
            Spec.Fold(Stack(s, n));
            return false;
        }

        /// <summary>The top item.</summary>
        public static int TopItem(CellStack s, int n)
        {
            Spec.Requires(n > 0 && Stack(s, n));
            Spec.Ensures(Stack(s, n));
            Spec.Unfold(Stack(s, n));
            int t = s.Items[n - 1];
            Spec.Fold(Stack(s, n));
            return t;
        }

        /// <summary>Pushing on b leaves a's cells and every other array (here, one in hand) as they were.</summary>
        public static int PushOnOne(CellStack a, CellStack b, int[] other)
        {
            Spec.Requires(Stack(a, 1) && Stack(b, 0) && other.Length > 0 && Spec.Acc(other));
            Spec.Ensures((int r) => Stack(a, 1) && Spec.Acc(other));
            Spec.Unfold(Stack(a, 1));
            int t = a.Items[0];
            Spec.Fold(Stack(a, 1));
            int o = other[0];
            bool pushed = PushItem(b, 0, 5);
            Spec.Unfold(Stack(a, 1));
            Spec.Assert(a.Items[0] == t && other[0] == o);
            Spec.Fold(Stack(a, 1));
            if (pushed) Spec.Unfold(Stack(b, 1)); else Spec.Unfold(Stack(b, 0));
            return t;
        }
    }
}
