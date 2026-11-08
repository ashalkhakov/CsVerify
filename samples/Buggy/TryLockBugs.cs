// The flag of the example in the documentation of System.Threading.Interlocked, used as a try-lock, with bugs:
// as published (no finally), the guarded count touched where the flag was refused, and its invariant broken.
using System.Threading;
using CsVerify;

namespace Samples.Buggy.TryLock
{
    public sealed class Resource
    {
        private int _usingResource;
        [GuardedBy(nameof(_usingResource))] private int _uses;
        [LockInvariant(nameof(_usingResource)), Pure] private bool Valid() => _uses >= 0;

        public Resource() { _uses = 0; }

        /// <summary>As in the documentation: released without a finally, so a throw in between locks everyone out for good.</summary>
        public bool AsPublished()
        {
            if (0 == Interlocked.Exchange(ref _usingResource, 1))
            {
                Interlocked.Exchange(ref _usingResource, 0);
                return true;
            }
            return false;
        }

        /// <summary>Counts a use where the flag was refused: another thread has it.</summary>
        public bool Denied()
        {
            if (Interlocked.Exchange(ref _usingResource, 1) == 0)
            {
                try { if (_uses < int.MaxValue) _uses++; }
                finally { Volatile.Write(ref _usingResource, 0); }
                return true;
            }
            _uses = 0;
            return false;
        }

        /// <summary>Gives the flag back with the count below zero.</summary>
        public void BrokenInvariant()
        {
            if (Interlocked.Exchange(ref _usingResource, 1) != 0) return;
            try { _uses = -1; }
            finally { Volatile.Write(ref _usingResource, 0); }
        }
    }
}
