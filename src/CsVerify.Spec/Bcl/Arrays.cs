#nullable enable
namespace CsVerify.Bcl
{
    using System;

    /// <summary>
    /// Contracts for <see cref="Array"/>'s static helpers. Each writes only the arrays its Spec.Modifies names; every other
    /// array keeps its contents. Out-of-range arguments are preconditions (the methods would throw).
    /// </summary>
    [ContractsFor(typeof(Array))]
    public static class ArrayContracts
    {
        public static T[] Empty<T>()
        {
            Spec.Ensures<T[]>(r => r.Length == 0);
            throw null!;
        }

        public static void Fill<T>(T[] array, T value)
        {
            Spec.Modifies(ObjSet.Of(array));
            Spec.Ensures(Spec.Forall(0, array.Length, i => Ghost.Of(array[i]) == Ghost.Of(value)));
            throw null!;
        }

        public static void Fill<T>(T[] array, T value, int startIndex, int count)
        {
            Spec.Requires(0 <= startIndex && 0 <= count && startIndex <= array.Length - count);
            Spec.Modifies(ObjSet.Of(array));
            Spec.Ensures(Spec.Forall(0, array.Length, i =>
                startIndex <= i && i < startIndex + count ? Ghost.Of(array[i]) == Ghost.Of(value) : Ghost.Of(array[i]) == Ghost.Of(Spec.Old(array[i]))));
            throw null!;
        }

        public static void Reverse<T>(T[] array)
        {
            Spec.Modifies(ObjSet.Of(array));
            Spec.Ensures(Spec.Forall(0, array.Length, i => Ghost.Of(array[i]) == Ghost.Of(Spec.Old(array[array.Length - 1 - i]))));
            throw null!;
        }

        // (the copied elements are not described: Copy converts between element types, int[] to long[] or object[],
        // and the converted values are not the ones stored; the rest of the destination is as it was)
        public static void Copy(Array sourceArray, Array destinationArray, int length)
        {
            Spec.Requires(0 <= length && length <= sourceArray.Length && length <= destinationArray.Length);
            Spec.Modifies(ObjSet.Of(destinationArray));
            Spec.Ensures(Spec.Forall(length, destinationArray.Length, i => Seq.Contents(destinationArray)[i] == Spec.Old(Seq.Contents(destinationArray))[i]));
            throw null!;
        }

        public static void Copy(Array sourceArray, int sourceIndex, Array destinationArray, int destinationIndex, int length)
        {
            Spec.Requires(0 <= sourceIndex && 0 <= destinationIndex && 0 <= length);
            Spec.Requires(sourceIndex <= sourceArray.Length - length && destinationIndex <= destinationArray.Length - length);
            Spec.Modifies(ObjSet.Of(destinationArray));
            Spec.Ensures(Spec.Forall(0, destinationArray.Length, i =>
                i < destinationIndex || destinationIndex + length <= i ? Seq.Contents(destinationArray)[i] == Spec.Old(Seq.Contents(destinationArray))[i] : true));
            throw null!;
        }

        public static void Resize<T>(ref T[]? array, int newSize)
        {
            Spec.Requires(newSize >= 0);
            Spec.Ensures(array != null && array.Length == newSize);
            throw null!;
        }

        [Pure]
        public static int IndexOf<T>(T[] array, T value)
        {
            Spec.Ensures<int>(r => -1 <= r && r < array.Length);
            throw null!;
        }

        // (how it orders elements is the comparer's: only the frame is given)
        public static void Sort<T>(T[] array)
        {
            Spec.Modifies(ObjSet.Of(array));
            throw null!;
        }
    }
}
