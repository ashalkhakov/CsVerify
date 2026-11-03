namespace Samples.Library
{
    using System.Collections.Generic;
    using CsVerify;

    public static class LibraryContractBugs
    {
        // an empty list has no first element: the indexer's precondition (CSV1001)
        public static int FirstOrZero(List<int> l) => l.Count >= 0 ? l[0] : 0;

        // a key that may be missing (CSV1001)
        public static int Lookup(Dictionary<string, int> d, string key) => d[key];

        // the list grows by one, not two (CSV1002)
        public static void AddTwice(List<int> l, int x)
        {
            Spec.Modifies(ObjSet.Of(l));
            Spec.Ensures(l.Count == Spec.Old(l.Count) + 2);
            l.Add(x);
        }

        // List.Add changes the list it is called on: not within this method's frame (CSV1017)
        public static void AddOutsideFrame(List<int> l, List<int> other)
        {
            Spec.Modifies(ObjSet.Of(l));
            other.Add(1);
        }

        // Substring past the end (CSV1001)
        public static string Tail(string s) => s.Substring(1);
    }
}
