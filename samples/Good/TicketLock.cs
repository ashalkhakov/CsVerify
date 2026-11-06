// A ticket lock, modeled as Leino does in "Modeling Concurrency in Dafny" (K. R. M. Leino, 2017): not threads, but the
// atomic events of every process. Safety: whatever order they happen in, at most one process is eating. Liveness: under
// a fair schedule, the display doesn't stall. Where he assumes a scheduler that is fair eventually, this one is fair
// within a window of w steps, which is stronger, and gives a number.
using System.Diagnostics;
using CsVerify;

namespace Samples.Good
{
    public sealed class TicketSystem
    {
        public const int Thinking = 0, Hungry = 1, Eating = 2;

        public readonly int[] Cs;    // each process's control state
        public readonly int[] T;     // the ticket it holds, when it isn't thinking
        public readonly int[] Who;   // who was given each ticket
        public int Ticket;           // the next ticket the dispenser gives
        public int Serving;          // the ticket the display shows

        /// <summary>What holds in every state: that each event keeps it is what makes this every interleaving.</summary>
        [GhostFunction]
        public bool Valid() =>
            Cs.Length == T.Length && Cs != T && Cs != Who && T != Who && 0 <= Serving && Serving <= Ticket && Ticket <= Who.Length &&
            Spec.Forall(0, Cs.Length, p => Cs[p] == Thinking || Cs[p] == Hungry || Cs[p] == Eating) &&
            // a ticket in hand is one that has been given and not yet served past
            Spec.Forall(0, Cs.Length, p => Cs[p] == Thinking || Serving <= T[p] && T[p] < Ticket) &&
            // no two processes hold one ticket
            Spec.Forall(0, Cs.Length, p => Spec.Forall(0, Cs.Length, q => p == q || Cs[p] == Thinking || Cs[q] == Thinking || T[p] != T[q])) &&
            // whoever eats holds the ticket being served
            Spec.Forall(0, Cs.Length, p => Cs[p] != Eating || T[p] == Serving) &&
            // every ticket given and not yet served is in the hand of whoever got it: the display always has someone to wait for
            Spec.Forall(Serving, Ticket, k => 0 <= Who[k] && Who[k] < Cs.Length && Cs[Who[k]] != Thinking && T[Who[k]] == k);

        public TicketSystem(int processes, int tickets)
        {
            Spec.Requires(processes >= 0 && tickets >= 0);
            Spec.Modifies(ObjSet.Empty);
            Spec.Ensures(Valid() && Cs.Length == processes && Who.Length == tickets && Ticket == 0 && Serving == 0);
            Spec.Ensures(Spec.Fresh(Cs) && Spec.Fresh(T) && Spec.Fresh(Who));
            Cs = new int[processes];
            T = new int[processes];
            Who = new int[tickets];
            Ticket = 0;
            Serving = 0;
        }

        /// <summary>A thinking process takes the next ticket.</summary>
        public void Request(int p)
        {
            Spec.Requires(Valid() && 0 <= p && p < Cs.Length && Cs[p] == Thinking && Ticket < Who.Length);
            Spec.Modifies(ObjSet.Of(this).Add(Cs).Add(T).Add(Who));
            Spec.Ensures(Valid() && Cs.Length == Spec.Old(Cs.Length) && Who.Length == Spec.Old(Who.Length));
            Spec.Ensures(Ticket == Spec.Old(Ticket) + 1 && Serving == Spec.Old(Serving) && Cs[p] == Hungry && T[p] == Spec.Old(Ticket));
            Spec.Ensures(Who[Spec.Old(Ticket)] == p && Spec.Forall(0, Who.Length, k => k == Spec.Old(Ticket) || Who[k] == Spec.Old(Who[k])));
            Spec.Ensures(Spec.Forall(0, Cs.Length, q => q == p || Cs[q] == Spec.Old(Cs[q]) && T[q] == Spec.Old(T[q])));
            T[p] = Ticket;
            Who[Ticket] = p;
            Ticket = Ticket + 1;
            Cs[p] = Hungry;
        }

        /// <summary>A hungry process whose ticket is being served goes in.</summary>
        public void Enter(int p)
        {
            Spec.Requires(Valid() && 0 <= p && p < Cs.Length && Cs[p] == Hungry && T[p] == Serving);
            Spec.Modifies(ObjSet.Of(this).Add(Cs).Add(T).Add(Who));
            Spec.Ensures(Valid() && Cs.Length == Spec.Old(Cs.Length) && Who.Length == Spec.Old(Who.Length));
            Spec.Ensures(Ticket == Spec.Old(Ticket) && Serving == Spec.Old(Serving) && Cs[p] == Eating && T[p] == Spec.Old(T[p]));
            Spec.Ensures(Spec.Forall(0, Who.Length, k => Who[k] == Spec.Old(Who[k])));
            Spec.Ensures(Spec.Forall(0, Cs.Length, q => q == p || Cs[q] == Spec.Old(Cs[q]) && T[q] == Spec.Old(T[q])));
            Cs[p] = Eating;
        }

        /// <summary>The process eating leaves, and advances the display.</summary>
        public void Leave(int p)
        {
            Spec.Requires(Valid() && 0 <= p && p < Cs.Length && Cs[p] == Eating);
            Spec.Modifies(ObjSet.Of(this).Add(Cs).Add(T).Add(Who));
            Spec.Ensures(Valid() && Cs.Length == Spec.Old(Cs.Length) && Who.Length == Spec.Old(Who.Length));
            Spec.Ensures(Ticket == Spec.Old(Ticket) && Serving == Spec.Old(Serving) + 1 && Cs[p] == Thinking);
            Spec.Ensures(Spec.Forall(0, Who.Length, k => Who[k] == Spec.Old(Who[k])));
            Spec.Ensures(Spec.Forall(0, Cs.Length, q => q == p || Cs[q] == Spec.Old(Cs[q]) && T[q] == Spec.Old(T[q])));
            Serving = Serving + 1;
            Cs[p] = Thinking;
        }

        /// <summary>The theorem of safety: in any state these events can reach, no two processes are eating.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public void MutualExclusion(int p, int q)
        {
            Spec.Requires(Valid() && 0 <= p && p < Cs.Length && 0 <= q && q < Cs.Length && Cs[p] == Eating && Cs[q] == Eating);
            Spec.Ensures(p == q);
        }

        /// <summary>A window of w steps from n in which p isn't scheduled.</summary>
        [GhostFunction]
        public static bool Missed(int[] schedule, int w, int n, int p)
        {
            Spec.Requires(0 <= n && n + w <= schedule.Length);
            return Spec.Forall(n, n + w, k => schedule[k] != p);
        }

        /// <summary>Every process is scheduled in every window of w steps: no window misses one.</summary>
        [GhostFunction]
        public static bool Fair(int[] schedule, int processes, int w) =>
            w > 0 && Spec.Forall(0, schedule.Length - w + 1, n => Spec.Forall(0, processes, p => !Missed(schedule, w, n, p)));

        /// <summary>A process not scheduled since a step can't have waited a whole window.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        private static void NotStarved(int[] schedule, int processes, int w, int since, int n, int p)
        {
            Spec.Requires(Fair(schedule, processes, w) && w > 0 && 0 <= since && since <= n && n <= schedule.Length && 0 <= p && p < processes);
            Spec.Requires(Spec.Forall(since, n, k => schedule[k] != p));
            Spec.Ensures(n - since < w);
            if (n - since >= w)
            {
                Spec.Assert(Spec.Forall(since, since + w, k => schedule[k] != p));
                Spec.Assert(Missed(schedule, w, since, p));
                Spec.Assert(Spec.Forall(0, schedule.Length - w + 1, m => Spec.Forall(0, processes, q => !Missed(schedule, w, m, q))));
            }
        }

        /// <summary>More windows are at least as long.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        private static void Longer(int a, int b, int w)
        {
            Spec.Requires(a <= b && w >= 0);
            Spec.Ensures(a * w <= b * w);
            Spec.Assert((b - a) * w >= 0);
        }

        /// <summary>The phase: 3 per ticket served, and within one, whether its holder is yet to come, hungry or eating.</summary>
        [GhostFunction]
        private bool InPhase(int phase)
        {
            Spec.Requires(0 <= Serving && Serving <= Ticket && Ticket <= Who.Length);
            return Serving == Ticket ? phase == 3 * Serving
                : 0 <= Who[Serving] && Who[Serving] < Cs.Length && (Cs[Who[Serving]] == Hungry ? phase == 3 * Serving + 1 : phase == 3 * Serving + 2);
        }

        /// <summary>
        /// One step of the process scheduled: the step its state allows. Either the phase moves on, or nothing the display
        /// waits for has changed, and the process wasn't what it is waiting for.
        /// </summary>
        private int Step(int p, int phase)
        {
            Spec.Requires(Valid() && 0 <= p && p < Cs.Length && Ticket < Who.Length && Who.Length <= 1000000 && InPhase(phase));
            Spec.Modifies(ObjSet.Of(this).Add(Cs).Add(T).Add(Who));
            Spec.Ensures(Valid() && Cs.Length == Spec.Old(Cs.Length) && Who.Length == Spec.Old(Who.Length) && Ticket <= Spec.Old(Ticket) + 1 && Serving >= Spec.Old(Serving));
            Spec.Ensures<int>(r => InPhase(r) && r >= phase);
            Spec.Ensures<int>(r => r > phase || Serving == Spec.Old(Serving) && Serving < Ticket && Who[Serving] == Spec.Old(Who[Serving]) && p != Who[Serving]);
            if (Cs[p] == Thinking)
            {
                bool first = Serving == Ticket;
                Request(p);
                return first ? phase + 1 : phase;
            }
            if (Cs[p] == Hungry)
            {
                if (T[p] != Serving) return phase;
                Enter(p);
                return phase + 1;
            }
            Leave(p);
            return Serving < Ticket ? 3 * Serving + 1 : 3 * Serving;
        }

        /// <summary>
        /// A run: at each step the process the schedule names takes its step. The theorem of liveness is that the display
        /// doesn't stall: it advances at least once in every 3 windows. Since every ticket held is at or past the display
        /// (Valid), no process stays hungry.
        /// </summary>
        public static TicketSystem Run(int processes, int[] schedule, int w)
        {
            Spec.Requires(processes > 0 && w > 0 && schedule.Length <= 1000000);
            Spec.Requires(Spec.Forall(0, schedule.Length, n => 0 <= schedule[n] && schedule[n] < processes));
            Spec.Requires(Fair(schedule, processes, w));
            Spec.Modifies(ObjSet.Empty);
            Spec.Ensures<TicketSystem>(r => r.Valid());
            Spec.Ensures<TicketSystem>(r => schedule.Length <= (3 * r.Serving + 3) * w);
            var s = new TicketSystem(processes, schedule.Length);
            int since = 0, phase = 0;
            for (int n = 0; n < schedule.Length; n++)
            {
                Spec.Invariant(0 <= n && n <= schedule.Length && 0 <= since && since <= n && s.Valid() && s.Ticket <= n);
                Spec.Invariant(s.Cs.Length == processes && s.Who.Length == schedule.Length && s.Cs != schedule && s.T != schedule && s.Who != schedule);
                Spec.Invariant(Spec.Forall(0, schedule.Length, m => 0 <= schedule[m] && schedule[m] < processes));
                Spec.Invariant(Fair(schedule, processes, w));
                Spec.Invariant(0 <= phase && since <= phase * w && n - since <= w && s.InPhase(phase));
                // whoever the display waits for hasn't been scheduled since the phase began (and without one, the phase is new)
                Spec.Invariant(s.Serving == s.Ticket ? since == n : Spec.Forall(since, n, k => schedule[k] != s.Who[s.Serving]));
                if (s.Serving != s.Ticket) NotStarved(schedule, processes, w, since, n, s.Who[s.Serving]);
                int next = s.Step(schedule[n], phase);
                if (next > phase)
                {
                    Longer(phase + 1, next, w);
                    Spec.Assert((phase + 1) * w == phase * w + w);
                    since = n + 1;
                    phase = next;
                }
            }
            Longer(phase + 1, 3 * s.Serving + 3, w);
            Spec.Assert((phase + 1) * w == phase * w + w);
            return s;
        }
    }
}
