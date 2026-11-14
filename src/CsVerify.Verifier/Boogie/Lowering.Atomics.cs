using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>[Atomic] fields: each read and write a step other threads may take between, Interlocked and Volatile.</summary>
    internal sealed partial class Lowering
    {
        // ------------------------------------------------------------------ atomic fields

        private KExpr Step(ISymbol field, KExpr old, KExpr now)
        {
            var step = Atomics.StepOf(field)?.OriginalDefinition;
            if (step == null)
            {
                return null;
            }
            if (!_isFunction(step))
            {
                throw new NotTranslated("an atomic field's step that isn't a function: " + step.Name);
            }
            return OrElse(Eq(old, now), new KFnCall
            {
                Callee = step,
                Args = new[] { old, now },
                At = _decl,
            });
        }

        /// <summary>
        /// The others take their steps: the field at the object is now the same as this thread last knew, or a step on;
        /// this thread now knows that value.
        /// </summary>
        private KExpr OthersStep(ISymbol field, KExpr o, bool onThis, SyntaxNode at)
        {
            var now = Declare("t$" + _temps++, FieldType(field));
            Emit(new KHavoc { Var = now });
            // (others store what may be stored there: not null, where the field is declared so)
            if (IsNullable(FieldType(field)) && NotNullable(FieldType(field)))
            {
                Emit(new KAssume { Cond = NotNull(new KVar(now)) });
            }
            var last = new KField
            {
                Field = field,
                Instance = o,
                OnThis = onThis,
                At = at,
                InstanceAt = at,
            };
            if (Step(field, last, new KVar(now)) is KExpr step)
            {
                Emit(new KSpecStmt
                {
                    Spec = step,
                    Assume = true,
                    At = at,
                    ArgumentAt = at,
                });
            }
            Emit(new KFieldStore
            {
                Field = field,
                Instance = o,
                OnThis = onThis,
                Value = new KVar(now),
                At = at,
                InstanceAt = at,
            });
            return new KVar(now);
        }

        private KExpr AtomicRead(ISymbol field, KExpr o, bool onThis, SyntaxNode at)
        {
            if (field is IFieldSymbol { IsVolatile: false })
            {
                Emit(new KCheck
                {
                    Cond = KLit.False,
                    Id = "CSV1030",
                    At = at,
                    NotAssumedAfter = true,
                    Message = $"'{at}' reads [Atomic] '{field.Name}' plainly, which the compiler may reorder or keep from an earlier read: declare it volatile, or read it with Volatile.Read or Interlocked",
                });
            }
            return OthersStep(field, o, onThis, at);
        }

        /// <summary>A plain write: one step from whatever the others have made it, which this thread doesn't read first (CSV1030).</summary>
        private KExpr AtomicWrite(ISymbol field, KExpr o, bool onThis, KExpr v, SyntaxNode at)
        {
            if (field is IFieldSymbol { IsVolatile: false })
            {
                Emit(new KCheck
                {
                    Cond = KLit.False,
                    Id = "CSV1030",
                    At = at,
                    NotAssumedAfter = true,
                    Message = $"'{at}' writes [Atomic] '{field.Name}' plainly, which the compiler may reorder: declare it volatile, or write it with Volatile.Write or Interlocked",
                });
            }
            var written = Declare("t$" + _temps++, FieldType(field));
            Emit(new KAssign
            {
                Var = written,
                Value = v,
            });
            var cur = OthersStep(field, o, onThis, at);
            if (Step(field, cur, new KVar(written)) is KExpr step)
            {
                Emit(new KCheck
                {
                    Cond = step,
                    Id = "CSV1030",
                    At = at,
                    Message = $"this write of [Atomic] '{field.Name}' might not be a step from what it overwrites, which another thread may have changed since this one read it: write it with Interlocked.CompareExchange, or a value any it could replace allows",
                });
            }
            return new KVar(written);
        }

        /// <summary>Volatile.Read/Write and Interlocked's operations on an atomic field: each one step after the others'; what it writes, a step (CSV1030).</summary>
        private KExpr AtomicCall(IInvocationOperation inv)
        {
            var ordered = inv.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
            var target = ordered[0].Value is IFlowCaptureReferenceOperation c && _captured.TryGetValue(c.Id, out var cv) ? cv : ordered[0].Value;
            // (a plain field by ref, as to any call: not supported, CSV1901; read here, which code that
            // runs alongside other code mustn't do unheld, CSV1027; the call's value unknown)
            if (Unconverted(target) is IFieldReferenceOperation pf0 && !Atomics.IsAtomic(pf0.Field) && InSubset(pf0.Type))
            {
                Emit(new KCheck
                {
                    Cond = KLit.False,
                    Id = "CSV1901",
                    At = ordered[0].Syntax,
                    NotAssumedAfter = true,
                    Message = $"passing '{ordered[0].Value.Syntax}' by ref is not supported: only locals, parameters, array elements and their structs' members",
                });
                Expr(Unconverted(target));
                foreach (var a in ordered.Skip(1))
                {
                    Expr(a.Value);
                }
                if (inv.Type == null || inv.Type.SpecialType == SpecialType.System_Void)
                {
                    return null;
                }
                var u = Declare("t$" + _temps++, inv.Type);
                Emit(new KHavoc { Var = u });
                return new KVar(u);
            }
            if (!(Unconverted(target) is IFieldReferenceOperation fr) || !Atomics.IsAtomic(fr.Field))
            {
                throw new NotTranslated("Interlocked of a field that isn't atomic");
            }
            var (field, o, onThis, _) = FieldOf(fr);
            // (each argument evaluated, in a variable of its own: the checks below are of values)
            var args = ordered.Skip(1).Select(a =>
            {
                var t = Declare("t$" + _temps++, a.Value.Type);
                Emit(new KAssign
                {
                    Var = t,
                    Value = Expr(a.Value),
                });
                return (KExpr)new KVar(t);
            }).ToArray();
            var type = FieldType(field);
            var cur = OthersStep(field, o, onThis, inv.Syntax);
            string what = $"'{inv.Syntax}' might not be a step of [Atomic] '{field.Name}'";
            void Write(KExpr v, KExpr when = null)
            {
                if (Step(field, cur, v) is KExpr step)
                {
                    Emit(new KCheck
                    {
                        Cond = when == null ? step : new KOp("==>", when, step),
                        Id = "CSV1030",
                        At = inv.Syntax,
                        Message = what,
                    });
                }
                Emit(new KFieldStore
                {
                    Field = field,
                    Instance = o,
                    OnThis = onThis,
                    Value = when == null ? v : new KOp("ite", when, v, cur),
                    At = inv.Syntax,
                    InstanceAt = inv.Syntax,
                });
            }
            var name = (inv.TargetMethod.ContainingType.Name == "Volatile" ? "Volatile." : "") + inv.TargetMethod.Name;
            switch (name)
            {
                case "Volatile.Read": case "Read": return cur;
                case "Volatile.Write":
                    Write(args[0]);
                    return null;
                case "Increment": case "Decrement": case "Add":
                {
                    // (wrapping at the type's ends, as at run time)
                    var delta = name == "Increment" ? KLit.One : name == "Decrement" ? KLit.MinusOne : args[0];
                    var t = Declare("t$" + _temps++, type);
                    Emit(new KAssign
                    {
                        Var = t,
                        Value = new KArith
                        {
                            Op = "+",
                            Left = cur,
                            Right = delta,
                            Type = type,
                            Mode = KMode.Unchecked,
                            At = inv.Syntax,
                        },
                    });
                    Write(new KVar(t));
                    return new KVar(t);
                }
                case "Exchange":
                    Write(args[0]);
                    return cur;
                case "CompareExchange":
                    Write(args[0], Eq(cur, args[1]));
                    return cur;
                // (bitwise, at once: the old value given back)
                case "And" or "Or" when IsIntegral(type):
                {
                    var t = Declare("t$" + _temps++, type);
                    Emit(new KAssign
                    {
                        Var = t,
                        Value = Bitwise(name == "And" ? BinaryOperatorKind.And : BinaryOperatorKind.Or, cur, args[0], type, inSpec: false),
                    });
                    Write(new KVar(t));
                    return cur;
                }
                default: throw new NotTranslated(name + " of an atomic field");
            }
        }
    }
}
