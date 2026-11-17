using System;
using System.IO;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Boogie.SMTLib;
using Microsoft.Boogie.VCExprAST;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// Boogie's SMT-LIB solvers, made to give up when their process dies (#58).
    /// </summary>
    /// <remarks>
    /// In Boogie 3.5.8 a solver that dies can hang a run for ever:
    /// - SMTLibProcess ignores the end of the solver's output, so a check waiting for an answer from a solver that died
    ///   never ends. Boogie awaits it with no time limit, and its checker's slot (one of /vcsCores) is never released.
    /// - Checker.GoBackToIdle pings the solver, and when the solver has died the ping throws an IOException or
    ///   ProverDiedException. It catches only a TimeoutException, so there too the slot is never released.
    /// Once every slot is lost, the run's threads and remaining solvers are idle and it waits for ever. Here a check
    /// or reset whose solver's output ends throws an IOException (Boogie: the procedure is skipped, so not verified),
    /// and a failed ping is a TimeoutException, on which Boogie closes the checker and releases its slot.
    /// </remarks>
    internal sealed class SolverFactory : Factory
    {
        private static readonly FieldInfo ProcessField = typeof(SMTLibProcess).GetField("solver", BindingFlags.Instance | BindingFlags.NonPublic);
        private static readonly FieldInfo ParserField = typeof(SMTLibProcess).GetField("sexpParser", BindingFlags.Instance | BindingFlags.NonPublic);

        /// <summary>Each solver's end of output: done when its process's output ends.</summary>
        private static readonly ConditionalWeakTable<SMTLibSolver, Task> Ends = new ConditionalWeakTable<SMTLibSolver, Task>();

        /// <summary>These solvers for the run these options are for.</summary>
        public static void Use(CommandLineOptions options)
        {
            options.TheProverFactory = new SolverFactory();
            var create = options.CreateSolver;
            options.CreateSolver = (libOptions, solverOptions) => Watched(create(libOptions, solverOptions));
        }

        private static SMTLibSolver Watched(SMTLibSolver solver)
        {
            if (solver is SMTLibProcess p && ProcessField?.GetValue(p) is System.Diagnostics.Process process && ParserField?.GetValue(p) is global::SMTLib.SExprParser parser)
            {
                var end = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
                process.OutputDataReceived += (_, e) =>
                {
                    if (e.Data == null)
                    {
                        // (the parser's end: the next read is null, the solver gone, on which a ping before a check
                        // restarts it)
                        parser.AddLine(null);
                        end.TrySetResult();
                    }
                };
                Ends.AddOrUpdate(solver, end.Task);
            }
            return solver;
        }

        protected override SMTLibProcessTheoremProver SpawnProver(SMTLibOptions libOptions, ProverOptions options, VCExpressionGenerator gen, SMTLibProverContext ctx) =>
            options.BatchMode ? base.SpawnProver(libOptions, options, gen, ctx) : new Solver(libOptions, (SMTLibSolverOptions)options, gen, ctx);

        private sealed class Solver : SMTLibInteractiveTheoremProver
        {
            public Solver(SMTLibOptions libOptions, SMTLibSolverOptions options, VCExpressionGenerator gen, SMTLibProverContext ctx)
                : base(libOptions, options, gen, ctx)
            {
            }

            public override async Task<SolverOutcome> Check(string descriptiveName, VCExpr vc, ErrorHandler handler, int errorLimit, CancellationToken cancellationToken)
            {
                var check = base.Check(descriptiveName, vc, handler, errorLimit, cancellationToken);
                await UnlessDied(check, "the check of " + descriptiveName);
                return await check;
            }

            public override async Task Reset(VCExpressionGenerator generator)
            {
                var reset = base.Reset(generator);
                await UnlessDied(reset, "a reset");
                await reset;
            }

            /// <summary>Once the work is done, or an IOException once its solver's output ends first.</summary>
            private async Task UnlessDied(Task work, string what)
            {
                // (its process may be restarted meanwhile: the one that ended is then not the one it waits on)
                for (var solver = Process; !work.IsCompleted && solver != null && Ends.TryGetValue(solver, out var end);)
                {
                    await Task.WhenAny(work, end);
                    if (work.IsCompleted)
                    {
                        return;
                    }
                    if (ReferenceEquals(solver, Process))
                    {
                        throw new IOException("the solver died during " + what);
                    }
                    solver = Process;
                }
            }

            public override async Task GoBackToIdle()
            {
                try
                {
                    await base.GoBackToIdle();
                }
                catch (Exception e) when (e is IOException || e is ProverDiedException || e is ObjectDisposedException || e is InvalidOperationException)
                {
                    throw new TimeoutException("the solver died: " + e.Message, e);
                }
            }
        }
    }
}
