// Dining philosophers, modeled in the style of Leino's "Modeling Concurrency in Dafny": atomic events, and what holds in
// every state they can reach. Taking the lower-numbered fork first, no two neighbours eat at once, and someone can always
// move: there is no deadlock. Taking the left fork first, everyone can pick up one fork, and then no one can move.
using System.Diagnostics;
using CsVerify;

namespace Samples.Good
{
    public sealed class DiningPhilosophers
    {
        public const int Thinking = 0, HasFirst = 1, Eating = 2, Free = -1;

        public readonly int N;
        public readonly bool Ordered;     // lower-numbered fork first, or everyone's left fork first
        public readonly int[] State;      // what each philosopher is doing
        public readonly int[] Fork;       // who holds each fork

        /// <summary>Philosopher p sits between forks p and p + 1 (round the table). Which it takes first, and which second.</summary>
        [Pure]
        public int First(int p)
        {
            Spec.Requires(0 <= p && p < N);
            return Ordered && p == N - 1 ? 0 : p;
        }

        [Pure]
        public int Second(int p)
        {
            Spec.Requires(0 <= p && p < N && N >= 2);
            return p < N - 1 ? p + 1 : Ordered ? N - 1 : 0;
        }

        /// <summary>What holds in every state.</summary>
        [GhostFunction]
        public bool Valid() =>
            N >= 2 && State.Length == N && Fork.Length == N && State != Fork &&
            Spec.Forall(0, N, p => State[p] == Thinking || State[p] == HasFirst || State[p] == Eating) &&
            // philosophers hold the forks their state says
            Spec.Forall(0, N, p => State[p] == Thinking || Fork[First(p)] == p) &&
            Spec.Forall(0, N, p => State[p] != Eating || Fork[Second(p)] == p) &&
            // and no others
            Spec.Forall(0, N, f => Fork[f] == Free || 0 <= Fork[f] && Fork[f] < N &&
                (f == First(Fork[f]) && State[Fork[f]] != Thinking || f == Second(Fork[f]) && State[Fork[f]] == Eating));

        public DiningPhilosophers(int n, bool ordered)
        {
            Spec.Requires(n >= 2);
            Spec.Modifies(ObjSet.Empty);
            Spec.Ensures(Valid() && N == n && Ordered == ordered && Spec.Fresh(State) && Spec.Fresh(Fork));
            Spec.Ensures(Spec.Forall(0, n, p => State[p] == Thinking && Fork[p] == Free));
            N = n;
            Ordered = ordered;
            State = new int[n];
            Fork = new int[n];
            for (int f = 0; f < n; f++)
            {
                Spec.Invariant(0 <= f && f <= n && N == n && Ordered == ordered && Fork.Length == n && State.Length == n && State != Fork);
                Spec.Invariant(Spec.Forall(0, n, p => State[p] == Thinking));
                Spec.Invariant(Spec.Forall(0, f, g => Fork[g] == Free));
                Fork[f] = Free;
            }
        }

        /// <summary>The events a philosopher can take in a state: this is what deadlock is the absence of.</summary>
        [GhostFunction]
        public bool CanMove(int p)
        {
            Spec.Requires(0 <= p && p < N && N >= 2 && Fork.Length == N && State.Length == N);
            return State[p] == Thinking ? Fork[First(p)] == Free : State[p] == HasFirst ? Fork[Second(p)] == Free : true;
        }

        public void PickFirst(int p)
        {
            Spec.Requires(Valid() && 0 <= p && p < N && State[p] == Thinking && Fork[First(p)] == Free);
            Spec.Modifies(ObjSet.Of(State).Add(Fork));
            Spec.Ensures(Valid() && State[p] == HasFirst && Fork[First(p)] == p);
            Spec.Ensures(Spec.Forall(0, N, q => q == p || State[q] == Spec.Old(State[q])));
            Spec.Ensures(Spec.Forall(0, N, f => f == First(p) || Fork[f] == Spec.Old(Fork[f])));
            Fork[First(p)] = p;
            State[p] = HasFirst;
        }

        public void PickSecond(int p)
        {
            Spec.Requires(Valid() && 0 <= p && p < N && State[p] == HasFirst && Fork[Second(p)] == Free);
            Spec.Modifies(ObjSet.Of(State).Add(Fork));
            Spec.Ensures(Valid() && State[p] == Eating);
            Fork[Second(p)] = p;
            State[p] = Eating;
        }

        public void PutDown(int p)
        {
            Spec.Requires(Valid() && 0 <= p && p < N && State[p] == Eating);
            Spec.Modifies(ObjSet.Of(State).Add(Fork));
            Spec.Ensures(Valid() && State[p] == Thinking);
            Fork[First(p)] = Free;
            Fork[Second(p)] = Free;
            State[p] = Thinking;
        }

        /// <summary>The theorem of safety: two philosophers eating don't share a fork, so neighbours never eat at once.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public void NoSharedFork(int p, int q)
        {
            Spec.Requires(Valid() && 0 <= p && p < N && 0 <= q && q < N && p != q && State[p] == Eating && State[q] == Eating);
            Spec.Ensures(First(p) != First(q) && First(p) != Second(q) && Second(p) != First(q) && Second(p) != Second(q));
        }

        /// <summary>
        /// The theorem of no deadlock, with lower-numbered forks first: whatever the state, here is a philosopher who can
        /// move. Look at the highest fork held. Whoever holds it is eating, or waits for a higher fork, which is free.
        /// </summary>
        public int SomeoneCanMove()
        {
            Spec.Requires(Valid() && Ordered);
            Spec.Modifies(ObjSet.Empty);
            Spec.Ensures<int>(r => 0 <= r && r < N && CanMove(r));
            for (int f = N - 1; f >= 0; f--)
            {
                Spec.Invariant(-1 <= f && f < N && Valid() && Ordered);
                Spec.Invariant(Spec.Forall(f + 1, N, g => Fork[g] == Free));
                if (Fork[f] != Free)
                {
                    int p = Fork[f];
                    Spec.Assert(First(p) < Second(p));
                    Spec.Assert(State[p] != HasFirst || f == First(p));
                    Spec.Assert(CanMove(p));
                    return p;
                }
            }
            Spec.Assert(Spec.Forall(0, N, g => Fork[g] == Free));
            Spec.Assert(Fork[First(0)] == Free);
            Spec.Assert(State[0] == Thinking);
            Spec.Assert(CanMove(0));
            return 0;
        }

        /// <summary>
        /// And the same table with left forks first: this run is allowed, and reaches a state where no one can move. So the
        /// theorem above isn't empty: it is the order of the forks that gives it.
        /// </summary>
        public static DiningPhilosophers LeftFirstDeadlocks()
        {
            Spec.Modifies(ObjSet.Empty);
            Spec.Ensures<DiningPhilosophers>(r => r.Valid() && r.N == 3 && !r.CanMove(0) && !r.CanMove(1) && !r.CanMove(2));
            var table = new DiningPhilosophers(3, false);
            Spec.Assert(table.First(0) == 0 && table.First(1) == 1 && table.First(2) == 2);
            Spec.Assert(table.Second(0) == 1 && table.Second(1) == 2 && table.Second(2) == 0);
            table.PickFirst(0);
            Spec.Assert(table.First(1) == 1 && table.First(2) == 2);
            table.PickFirst(1);
            Spec.Assert(table.First(2) == 2);
            table.PickFirst(2);
            Spec.Assert(table.Fork[0] == 0 && table.Fork[1] == 1 && table.Fork[2] == 2);
            Spec.Assert(table.Second(0) == 1 && table.Second(1) == 2 && table.Second(2) == 0);
            return table;
        }
    }

    /// <summary>
    /// The same table in real code: a fork is a lock, and a philosopher eats holding two. Taken in increasing order
    /// (checked: CSV1025), so that no cycle of waiting can form, which is the argument SomeoneCanMove proves of the model.
    /// </summary>
    public sealed class Table
    {
        private readonly object[] _forks;
        private readonly int[] _meals;

        public Table(int seats)
        {
            Spec.Requires(seats >= 2);
            Spec.Ensures(_forks.Length == seats && _meals.Length == seats);
            _forks = new object[seats];
            _meals = new int[seats];
            for (int i = 0; i < seats; i++)
            {
                Spec.Invariant(0 <= i && i <= seats && _forks.Length == seats && _meals.Length == seats);
                Spec.Invariant(Spec.Forall(0, i, k => _forks[k] != null));
                _forks[i] = new object();
            }
        }

        /// <summary>One meal for the philosopher in a seat, between its two forks.</summary>
        public void Dine(int seat)
        {
            Spec.Requires(0 <= seat && seat < _forks.Length && _forks.Length >= 2 && _meals.Length == _forks.Length);
            Spec.Requires(Spec.Forall(0, _forks.Length, k => _forks[k] != null));
            int right = seat == _forks.Length - 1 ? 0 : seat + 1;
            int first = seat < right ? seat : right;
            int second = seat < right ? right : seat;
            lock (_forks[first])
            {
                lock (_forks[second])
                {
                    if (_meals[seat] < int.MaxValue) _meals[seat]++;
                }
            }
        }

        public int Meals(int seat)
        {
            Spec.Requires(0 <= seat && seat < _meals.Length && _forks.Length >= 2 && _meals.Length == _forks.Length);
            Spec.Requires(Spec.Forall(0, _forks.Length, k => _forks[k] != null));
            int right = seat == _forks.Length - 1 ? 0 : seat + 1;
            int first = seat < right ? seat : right;
            int second = seat < right ? right : seat;
            lock (_forks[first])
            {
                lock (_forks[second]) { return _meals[seat]; }
            }
        }
    }
}
