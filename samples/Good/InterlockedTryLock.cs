// After the example in the documentation of System.Threading.Interlocked (learn.microsoft.com), a flag used as a
// try-lock. As published, the flag isn't given back if the work throws, so every thread is locked out for good: here
// the work is in a try whose finally gives it back, and a count stands for the resource that isn't thread safe. The
// count is proved used only while the flag is held, and its invariant kept. Each thread is handed its name rather than
// reading Thread.CurrentThread.Name, which the verifier doesn't model.
using System;
using System.Threading;
using CsVerify;

namespace Samples.Good.TryLock
{
    class MyInterlockedExchangeExampleClass
    {
        //0 for false, 1 for true.
        private static int usingResource = 0;
        [GuardedBy(nameof(usingResource))] private static int uses;
        [LockInvariant(nameof(usingResource)), Pure] private static bool Valid() => uses >= 0;
        static MyInterlockedExchangeExampleClass() { uses = 0; }

        private const int numThreadIterations = 5;
        private const int numThreads = 10;

        static void Main()
        {
            Random rnd = new Random();
            for (int i = 0; i < numThreads; i++)
            {
                string name = String.Format("Thread{0}", i + 1);
                Thread myThread = new Thread(() => MyThreadProc(name));
                Thread.Sleep(rnd.Next(0, 1000));
                myThread.Start();
            }
        }

        [RunsConcurrently]
        private static void MyThreadProc(string name)
        {
            for (int i = 0; i < numThreadIterations; i++)
            {
                UseResource(name);
                Thread.Sleep(1000);
            }
        }

        [RunsConcurrently]
        static bool UseResource(string name)
        {
            if (0 == Interlocked.Exchange(ref usingResource, 1))
            {
                try
                {
                    Console.WriteLine("{0} acquired the lock", name);
                    //Code to access a resource that is not thread safe would go here.
                    if (uses < int.MaxValue) uses = uses + 1;
                    Thread.Sleep(500);
                    Console.WriteLine("{0} exiting lock", name);
                }
                finally
                {
                    //Release the lock, even if the work throws
                    Interlocked.Exchange(ref usingResource, 0);
                }
                return true;
            }
            else
            {
                Console.WriteLine("   {0} was denied the lock", name);
                return false;
            }
        }
    }
}
