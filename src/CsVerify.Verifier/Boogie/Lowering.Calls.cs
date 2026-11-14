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
    /// <summary>Calls: of the program's methods (by their contracts), of library members (by stubs, or as library calls).</summary>
    internal sealed partial class Lowering
    {
        /// <summary>
        /// A [Pure] member of string whose stub contract the library gives (its parameters and result in the subset): a
        /// function of its arguments, which its contract describes.
        /// </summary>
        private bool IsStub(IMethodSymbol m) =>
            // (a string's [Pure] members; and a library's static ones over spans, BinaryPrimitives' reads say)
            // (and any static one of the library's, Math.Clamp say)
            (IsString(m.ContainingType) || m.IsStatic && !m.IsGenericMethod && m.DeclaringSyntaxReferences.Length == 0) &&
            _contractOf?.Invoke(m) is Contract c && c.IsStub && c.IsPure && !m.ReturnsVoid && InSubset(m.ReturnType) &&
            m.Parameters.All(x => x.RefKind == RefKind.None && InSubset(x.Type)) && c.Stub.Parameters.All(x => x.RefKind == RefKind.None && InSubset(x.Type));

        /// <summary>
        /// A library property without a stub that may change (not a field, nor a string's, an array's, a collection's or
        /// anything the kernel reads otherwise), of the subset's types: unknown where code reads it.
        /// </summary>
        private bool LibraryProperty(IPropertyReferenceOperation p) =>
            UnstubbedLibraryGetter(p) && (p.Instance == null || InSubset(p.Instance.Type) || IsLibraryObject(p.Instance.Type)) && !ReadOtherwise(p);

        /// <summary>
        /// A library's property with a getter, not a field, of the subset's type, not CsVerify's, with no stub that says
        /// something of it (a stub that says nothing, CancellationTokenSource.Token's, is as none).
        /// </summary>
        private bool UnstubbedLibraryGetter(IPropertyReferenceOperation p) =>
            p.Property.DeclaringSyntaxReferences.Length == 0 && p.Property.GetMethod != null && !IsField(p.Property.OriginalDefinition) && InSubset(p.Type) &&
            !(_contractOf?.Invoke(p.Property.GetMethod.OriginalDefinition) is Contract c && c.IsStub && (c.Ensures.Count > 0 || c.Requires.Count > 0)) &&
            p.Property.ContainingType.ContainingNamespace?.ToDisplayString() != SpecSymbols.Namespace;

        /// <summary>
        /// A property the kernel reads another way: a string's, an array's Length (or anything of an array or span), a
        /// collection's or its interface's, a pair's, a memory value's, a task's, an int?'s, a data value's, a tuple's, EF's.
        /// </summary>
        private bool ReadOtherwise(IPropertyReferenceOperation p) =>
            IsString(p.Instance?.Type) || IsString(p.Property.ContainingType) || p.Property.Name == "Length" && IsArray(ActualArray(p.Instance?.Type)) ||
            CollectionOf(p.Instance?.Type) != null || IsCollection(p.Property.ContainingType) || IsCollectionInterface(p.Property.ContainingType) ||
            IsPair(p.Instance?.Type) || IsMemValue(p.Instance?.Type) || IsGivenTask(p.Instance?.Type) || IsNullableValue(p.Instance?.Type) ||
            IsSpan(p.Instance?.Type) || IsMultiArray(p.Instance?.Type) || IsArray(p.Instance?.Type) || IsData(p.Property.ContainingType) || IsTuple(p.Instance?.Type) ||
            KernelTypes.Ef != null && (KernelTypes.Ef.IsContextType(p.Property.ContainingType) || IsQueryHandle(p.Type) || IsEfTransaction(p.Instance?.Type) || IsEfTransaction(p.Type));

        /// <summary>
        /// A delegate handed to a library member: the member's call of it must be allowed. A
        /// stub that says what it needs of it (Spec.Pre, Spec.Total) has that proved, as its preconditions are; Parallel.For
        /// calls it with each index in its range; otherwise the library may pass it anything, so it must be total (CSV1029).
        /// </summary>
        private void HandedToLibrary(IMethodSymbol m, List<IArgumentOperation> ordered, KExpr[] args)
        {
            var callee = _contractOf?.Invoke(m);
            foreach (var a in ordered)
            {
                if (!(a.Parameter?.Type is INamedTypeSymbol type) || !IsDelegate(type) || type.DelegateInvokeMethod == null)
                {
                    continue;
                }
                if (callee != null && callee.IsStub && callee.Requires.Any(r => r.DescendantsAndSelf().OfType<IInvocationOperation>().Any(i =>
                        SpecSymbols.IsSpecClass(i.TargetMethod.ContainingType) && i.TargetMethod.Name is "Pre" or "Total" && i.Arguments.Length > 0 &&
                        Unconverted(i.Arguments[0].Value) is IParameterReferenceOperation p && p.Parameter.Name == a.Parameter.Name)))
                {
                    continue;
                }
                var value = Unconverted(a.Value);
                bool made = value is IDelegateCreationOperation;
                if (made && LambdaOf(((IDelegateCreationOperation)value).Target) is IAnonymousFunctionOperation af && _contractOf?.Invoke(af.Symbol) is Contract lc && lc.OwnRequires.Count == 0)
                {
                    continue;
                }
                var key = FuncKey(type);
                _p.DelegateKeys.Add(key);
                var d = args[a.Parameter.Ordinal];
                if (!(made || value is ILocalReferenceOperation or IParameterReferenceOperation or IFieldReferenceOperation))
                {
                    Emit(KCheck.Of(
                        KLit.False,
                        "CSV1029",
                        a.Syntax,
                        notAssumedAfter: true,
                        message: $"'{m.Name}' may call '{a.Value.Syntax}' with any arguments, but it isn't known to accept them all: keep it in a local said to be Spec.Total"));
                    continue;
                }
                // (Parallel.For(from, to, body): body(i) for each i in [from, to))
                if (m.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Parallel" && m.Name == "For" && a.Parameter.Ordinal == 2 &&
                    type.DelegateInvokeMethod.Parameters.Length == 1 && type.DelegateInvokeMethod.Parameters[0].Type.SpecialType == SpecialType.System_Int32)
                {
                    var (lo, hi) = (args[0], args[1]);
                    Emit(KCheck.Of(
                        KQuant.ForAll(
                     "q$i",
                     Implies(AndAlso(Le(lo, new KVar("q$i")), Lt(new KVar("q$i"), hi)), new KOp("$pre." + key, d, new KVar("q$i")))),
                        "CSV1001",
                        a.Syntax,
                        $"'{m.Name}' calls this with each index from {ordered[0].Value.Syntax} up to {ordered[1].Value.Syntax}, but it might not accept them all"));
                    continue;
                }
                Emit(KCheck.Of(
                    new KOp("$total." + key, d),
                    "CSV1029",
                    a.Syntax,
                    made ? $"'{m.Name}' may call this with any arguments, but its precondition might not hold for them all"
                                       : $"'{m.Name}' may call '{a.Value.Syntax}' with any arguments, but it isn't known to accept them all: say so with Spec.Requires(Spec.Total({a.Value.Syntax}))"));
            }
        }

        /// <summary>
        /// A library member that calls the delegate it is given with each element of a List or an array (the receiver, or
        /// the array first given), or each index of Parallel.For's range: "each", "write" where it also writes the
        /// sequence (Sort, RemoveAll), "index" for Parallel.For; null for any other.
        /// </summary>
        private string ElementwiseKind(IInvocationOperation call)
        {
            var m = call.TargetMethod;
            var del = call.Arguments.Where(a => a.Parameter != null && IsFunc(a.Parameter.Type)).ToList();
            if (del.Count != 1 || call.Arguments.Any(a => a.Parameter.RefKind != RefKind.None))
            {
                return null;
            }
            var owner = m.ContainingType?.OriginalDefinition.ToDisplayString();
            if (owner == "System.Threading.Tasks.Parallel" && m.Name == "For" && call.Arguments.Length == 3 && m.ReturnType.Name == "ParallelLoopResult" &&
                del[0].Parameter.Ordinal == 2 && ((INamedTypeSymbol)del[0].Parameter.Type).DelegateInvokeMethod.Parameters.Length == 1 &&
                ((INamedTypeSymbol)del[0].Parameter.Type).DelegateInvokeMethod.Parameters[0].Type.SpecialType == SpecialType.System_Int32)
            {
                return "index";
            }
            // (LINQ's Any, All and Count of an array or a List, with a lambda that isn't pure)
            if (owner == "System.Linq.Enumerable" && m.IsStatic && call.Arguments.Length == 2 && m.Name is "Any" or "All" or "Count" or "LongCount" &&
                del[0].Parameter.Ordinal == 1 && PureLambda(del[0].Value) == null && Unconverted(call.Arguments.First(a => a.Parameter.Ordinal == 0).Value) is var ls &&
                (IsList(ls.Type) || ls.Type is IArrayTypeSymbol { Rank: 1 }) && ElementOf(ls.Type) is ITypeSymbol le && InSubset(le))
            {
                return "each";
            }
            bool onList = owner == "System.Collections.Generic.List<T>" && call.Instance != null && IsList(call.Instance.Type) && call.Arguments.Length == 1;
            bool onArray = owner == "System.Array" && m.IsStatic && call.Arguments.Length == 2 && IsArray(call.Arguments.First(a => a.Parameter.Ordinal == 0).Value.Type) &&
                           ((IArrayTypeSymbol)call.Arguments.First(a => a.Parameter.Ordinal == 0).Value.Type).Rank == 1;
            if (!onList && !onArray)
            {
                return null;
            }
            if (ElementOf(onList ? call.Instance.Type : call.Arguments.First(a => a.Parameter.Ordinal == 0).Value.Type) is not ITypeSymbol elem || !InSubset(elem))
            {
                return null;
            }
            return m.Name switch
            {
                "ForEach" or "Exists" or "Find" or "FindIndex" or "FindLast" or "FindLastIndex" or "TrueForAll" => "each",
                "Sort" or "RemoveAll" => "write",
                _ => null,
            };
        }

        /// <summary>
        /// A library member that calls a delegate with each element (or index): the
        /// delegate must accept each, where it changes nothing (a lambda that writes may change what the next is called
        /// with: total), or anything; what it gives back isn't known; what the delegate may change, changes, and what the
        /// member writes.
        /// </summary>
        private KExpr Elementwise(IInvocationOperation call)
        {
            var kind = ElementwiseKind(call);
            var m = call.TargetMethod;
            var at = call.Syntax;
            if (_p.UsesPerm && kind == "write")
            {
                throw new NotTranslated("a library call that writes, of a delegate, with permissions");
            }
            var da = call.Arguments.First(a => IsFunc(a.Parameter.Type));
            var type = (INamedTypeSymbol)da.Parameter.Type;
            var key = FuncKey(type);
            _p.DelegateKeys.Add(key);
            _p.CallsDelegates = true;
            Assumed(m);
            var srcArg = kind == "index" || call.Instance != null ? null : call.Arguments.First(a => a.Parameter.Ordinal == 0);
            var srcOp = kind == "index" ? null : call.Instance ?? Unconverted(srcArg.Value);
            var others = call.Arguments.Where(a => a != da && a != srcArg).OrderBy(a => a.Parameter.Ordinal).ToList();
            var ops = (srcOp == null ? new IOperation[0] : new[] { srcOp }).Concat(others.Select(a => a.Value)).Append(da.Value).ToArray();
            var vals = Operands(ops);
            var d = vals[vals.Length - 1];
            var src = srcOp == null ? null : vals[0];
            // (the sequence and the delegate: not null, or it throws ArgumentNullException)
            if (src != null)
            {
                Emit(KCheck.Of(NotNull(src), "CSV1013", srcOp.Syntax, $"'{srcOp.Syntax}' might be null: '{m.Name}' would throw"));
            }
            Emit(KCheck.Of(NotNull(d), "CSV1013", da.Syntax, $"'{da.Value.Syntax}' might be null: '{m.Name}' would throw"));
            var (lambda, quiet, free) = Handed(da);
            if (!free)
            {
                KExpr each = null;
                string what = null;
                if (kind == "index")
                {
                    var (lo, hi) = (vals[0], vals[1]);
                    each = KQuant.ForAll(
                        "q$i",
                        Implies(AndAlso(Le(lo, new KVar("q$i")), Lt(new KVar("q$i"), hi)), new KOp("$pre." + key, d, new KVar("q$i"))));
                    what = $"each index from {others[0].Value.Syntax} up to {others[1].Value.Syntax}";
                }
                else if (kind == "each" && quiet && type.DelegateInvokeMethod.Parameters.Length == 1)
                {
                    var st = srcOp.Type;
                    KExpr len; System.Func<KExpr, KExpr> Elem;
                    if (IsArray(st))
                    {
                        len = Length(src);
                        Elem = i => Sel(Elements(st), src, i);
                    }
                    else
                    {
                        foreach (var model in ModelsOf((INamedTypeSymbol)st))
                        {
                            _p.Models[model.Name] = model;
                        }
                        len = Sel(SizeMap, src);
                        var items = ModelOf("Items", (INamedTypeSymbol)st).Name;
                        Elem = i => Sel(items, src, i);
                    }
                    each = KQuant.ForAll(
                        "q$i",
                        Implies(AndAlso(Le(KLit.Zero, new KVar("q$i")), Lt(new KVar("q$i"), len)), new KOp("$pre." + key, d, Elem(new KVar("q$i")))));
                    what = $"each element of {srcOp.Syntax}";
                }
                if (each != null)
                {
                    Emit(KCheck.Of(each, "CSV1001", da.Syntax, $"'{m.Name}' calls this with {what}, but it might not accept them all"));
                }
                else
                {
                    Emit(KCheck.Of(
                        new KOp("$total." + key, d),
                        "CSV1029",
                        da.Syntax,
                        lambda != null ? $"'{m.Name}' may call this with anything (it may change what it is called with), but its precondition might not hold for them all"
                                                     : $"'{m.Name}' may call '{da.Value.Syntax}' with any arguments, but it isn't known to accept them all: say so with Spec.Requires(Spec.Total({da.Value.Syntax}))"));
                }
            }
            // (what the delegate may change, and what the member writes: anything, unless the delegate changes nothing)
            // (holding permissions: the delegate is given none, so it may only be one that changes nothing)
            if (_p.UsesPerm)
            {
                Emit(KCheck.Of(
                    new KOp("$nochange", d),
                    "CSV1016",
                    da.Syntax,
                    $"'{m.Name}' calls '{da.Value.Syntax}', which may write anything, which this method's permissions don't allow (say it changes nothing with Spec.ChangesNothing)"));
            }
            else if (kind == "write")
            {
                _p.HavocsAll = true;
                Emit(new KHavocAll());
            }
            else if (!quiet)
            {
                _p.HavocsAll = true;
                Emit(new KHavocAll { Unless = new KOp("$nochange", d) });
            }
            ForgetCaptured();
            if (call.Type == null || call.Type.SpecialType == SpecialType.System_Void || !InSubset(call.Type))
            {
                return null;
            }
            var r = Declare("t$" + _temps++, call.Type);
            Emit(KHavoc.Of(r));
            if (m.Name is "FindIndex" or "FindLastIndex" && src != null)
            {
                var len = IsArray(srcOp.Type) ? Length(src) : Sel(SizeMap, src);
                Emit(KAssume.Of(AndAlso(Le(KLit.MinusOne, new KVar(r)), Lt(new KVar(r), len))));
            }
            return new KVar(r);
        }

        /// <summary>
        /// A delegate a library object keeps (Lazy's factory), to call later: it must write nothing, as nothing says when
        /// it runs; what the constructor's stub says it accepts (Spec.Pre), or anything (CSV1029).
        /// </summary>
        private void StoredInLibrary(IMethodSymbol ctor, IArgumentOperation x, KExpr d)
        {
            var (lambda, quiet, free) = Handed(x);
            if (!quiet)
            {
                throw new NotTranslated("a delegate that may write, kept by a library object");
            }
            if (free)
            {
                return;
            }
            var type = (INamedTypeSymbol)x.Parameter.Type;
            var key = FuncKey(type);
            _p.DelegateKeys.Add(key);
            var stub = _contractOf?.Invoke(ctor);
            bool pre = stub != null && stub.IsStub && type.DelegateInvokeMethod.Parameters.Length == 0 && stub.Requires.Any(r => r.DescendantsAndSelf().OfType<IInvocationOperation>().Any(i =>
                SpecSymbols.IsSpecClass(i.TargetMethod.ContainingType) && i.TargetMethod.Name is "Pre" or "Total" && i.Arguments.Length == 1 &&
                Unconverted(i.Arguments[0].Value) is IParameterReferenceOperation p && p.Parameter.Name == x.Parameter.Name));
            if (pre)
            {
                Assumed(ctor);
                Emit(KCheck.Of(
                    new KOp("$pre." + key, d),
                    "CSV1001",
                    x.Syntax,
                    $"'{ctor.ContainingType.Name}' calls '{x.Value.Syntax}', but its precondition might not hold"));
            }
            else
            {
                Emit(KCheck.Of(
                    new KOp("$total." + key, d),
                    "CSV1029",
                    x.Syntax,
                    $"'{ctor.ContainingType.Name}' may call '{x.Value.Syntax}' with anything, but it isn't known to accept them all"));
            }
        }

        /// <summary>
        /// A collection's member without a stub (List.TrimExcess): it may change the collection it is called on, as any
        /// library member handed it may (against the caller's frame, CSV1017), and nothing else; what it gives isn't known.
        /// </summary>
        private KExpr CollectionUnstubbed(IMethodSymbol callee, IOperation instance, IReadOnlyList<IArgumentOperation> arguments, SyntaxNode at)
        {
            var recv = Expr(Unconverted(instance));
            Emit(KCheck.Of(NotNull(recv), "CSV1013", instance.Syntax, $"'{instance.Syntax}' might be null in '{at}'"));
            // (an argument boxed for it, to object: what it is, as the library's use of it isn't modeled)
            foreach (var a in arguments.OrderBy(a => a.Parameter.Ordinal))
            {
                Expr(a.Value is IConversionOperation { IsImplicit: true, Type.SpecialType: SpecialType.System_Object } box && InSubset(box.Operand.Type) ? box.Operand : a.Value);
            }
            foreach (var model in ModelsOf((INamedTypeSymbol)callee.ContainingType))
            {
                _p.Models[model.Name] = model;
                var row = model.Type.Substring("[Ref]".Length);
                Emit(KRow.Of(model.Name, recv, new KVar(LinqMap(row)), at: at));
            }
            if (SizeModelOf(callee) is string size)
            {
                Emit(KAssume.Of(Ge(Sel(size, recv), KLit.Zero)));
            }
            if (callee.ReturnsVoid)
            {
                return null;
            }
            var r = Declare("t$" + _temps++, callee.ReturnType);
            Emit(KHavoc.Of(r));
            return new KVar(r);
        }

        private string SizeModelOf(IMethodSymbol m) => ModelsOf((INamedTypeSymbol)m.ContainingType).Any(x => x.Name == SizeMap) ? SizeMap : null;

        /// <summary>
        /// Array.Reverse(a), Array.Copy(src, dst, n) and (src, i, dst, j, n), Array.Resize(ref a, n), as their stubs have
        /// them: the array's elements now (Reverse's, the old ones the other way round; Copy's, those it doesn't copy as
        /// they were, the copied ones not known, as Copy converts); a new array of the size, nothing known of its
        /// elements, for Resize. Their preconditions, CSV1001; a null array, CSV1014.
        /// </summary>
        private (bool, KExpr) ArrayHelper(IInvocationOperation call)
        {
            var m = call.TargetMethod;
            var ordered = call.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
            // (Sort(a): a written, its order the comparer's, as its stub has it)
            if (m.Name == "Sort" && ordered.Count == 1 && IsArray(Unconverted(ordered[0].Value).Type))
            {
                var at = Unconverted(ordered[0].Value).Type;
                var a = Expr(Unconverted(ordered[0].Value));
                CheckNotNull(ordered[0], a, m);
                var map = Elements(at);
                Emit(KRow.Of(map, a, new KVar(LinqMap("[int]" + ElementValue(map))), at: call.Syntax));
                return (true, null);
            }
            // (IndexOf(a, v): -1, or an index of a, as its stub has it)
            if (m.Name == "IndexOf" && ordered.Count == 2 && IsArray(Unconverted(ordered[0].Value).Type) && m.ReturnType.SpecialType == SpecialType.System_Int32)
            {
                var a = Expr(Unconverted(ordered[0].Value));
                CheckNotNull(ordered[0], a, m);
                Expr(ordered[1].Value);
                var r = Declare("t$" + _temps++, m.ReturnType);
                Emit(KHavoc.Of(r));
                Emit(KAssume.Of(AndAlso(Le(KLit.MinusOne, new KVar(r)), Lt(new KVar(r), Length(a)))));
                return (true, new KVar(r));
            }
            if (m.Name == "Reverse" && ordered.Count == 1 && IsArray(Unconverted(ordered[0].Value).Type))
            {
                var at = Unconverted(ordered[0].Value).Type;
                var a = Expr(Unconverted(ordered[0].Value));
                CheckNotNull(ordered[0], a, m);
                var map = Elements(at);
                var was = Declare("t$" + _temps++, _model.Compilation.GetSpecialType(SpecialType.System_Int32));
                var old = new KVar(LinqMap("[int]" + ElementValue(map)));
                Emit(KSpecStmt.AssumedFree(
                    KQuant.ForAll(
                 "i$r",
                 Eq(Sel(old, new KVar("i$r")), Sel(map, a, new KVar("i$r")))),
                    call.Syntax,
                    argumentAt: call.Syntax));
                var row = new KVar(LinqMap("[int]" + ElementValue(map)));
                Emit(KRow.Of(map, a, row, at: call.Syntax));
                var i = new KVar("i$r");
                Emit(KSpecStmt.AssumedFree(
                    KQuant.ForAll(
                 "i$r",
                 Implies(AndAlso(Le(KLit.Zero, i), Lt(i, Length(a))),
                                                                                            Eq(Sel(row, i), Sel(old, Minus(Minus(Length(a), KLit.One), i))))),
                    call.Syntax,
                    argumentAt: call.Syntax));
                return (true, null);
            }
            if (m.Name == "Copy" && ordered.Count is 3 or 5 && ordered.All(a => a.Parameter.RefKind == RefKind.None) &&
                IsArray(Unconverted(ordered[0].Value).Type) && IsArray(Unconverted(ordered[ordered.Count == 3 ? 1 : 2].Value).Type))
            {
                var src = Expr(Unconverted(ordered[0].Value));
                CheckNotNull(ordered[0], src, m);
                KExpr si = ordered.Count == 5 ? Expr(ordered[1].Value) : KLit.Zero;
                var dstArg = ordered[ordered.Count == 3 ? 1 : 2];
                var dst = Expr(Unconverted(dstArg.Value));
                CheckNotNull(dstArg, dst, m);
                KExpr di = ordered.Count == 5 ? Expr(ordered[3].Value) : KLit.Zero;
                var n = Expr(ordered[ordered.Count - 1].Value);
                CheckPrecondition(AndAlso(AndAlso(Le(KLit.Zero, si), Le(KLit.Zero, di)),
                            AndAlso(Le(KLit.Zero, n), AndAlso(Le(si, Minus(Length(src), n)), Le(di, Minus(Length(dst), n))))), "0 <= sourceIndex && 0 <= destinationIndex && 0 <= length && sourceIndex <= sourceArray.Length - length && destinationIndex <= destinationArray.Length - length", call.Syntax, m.Name);
                var dt = Unconverted(dstArg.Value).Type;
                var map = Elements(dt);
                var old = new KVar(LinqMap("[int]" + ElementValue(map)));
                var i = new KVar("i$c");
                Emit(KSpecStmt.AssumedFree(KQuant.ForAll("i$c", Eq(Sel(old, i), Sel(map, dst, i))), call.Syntax, argumentAt: call.Syntax));
                var row = new KVar(LinqMap("[int]" + ElementValue(map)));
                Emit(KRow.Of(map, dst, row, at: call.Syntax));
                Emit(KSpecStmt.AssumedFree(
                    KQuant.ForAll(
                 "i$c",
                 Implies(OrElse(Lt(i, di), Le(Plus(di, n), i)),
                                                                                            Eq(Sel(row, i), Sel(old, i)))),
                    call.Syntax,
                    argumentAt: call.Syntax));
                return (true, null);
            }
            if (m.Name == "Resize" && ordered.Count == 2 && ordered[0].Parameter.RefKind == RefKind.Ref && m.IsGenericMethod && IsArray(ordered[0].Value.Type))
            {
                var n = Expr(ordered[1].Value);
                CheckPrecondition(Ge(n, KLit.Zero), "newSize >= 0", call.Syntax, m.Name);
                var target = RefVariable(ordered[0]);
                var t = Declare("t$" + _temps++, ordered[0].Value.Type);
                Emit(KNew.Of(t, ordered[0].Value.Type, n));
                var map = Elements(ordered[0].Value.Type);
                Emit(KRow.Of(map, new KVar(t), new KVar(LinqMap("[int]" + ElementValue(map)))));
                Emit(KAssign.Of(target, new KVar(t)));
                var writeBacks = _writeBacks.ToList();
                _writeBacks.Clear();
                foreach (var (wt, wv) in writeBacks)
                {
                    Assign(wt, new KVar(wv));
                }
                return (true, null);
            }
            return (false, null);
        }

        private void CheckNotNull(IArgumentOperation a, KExpr v, IMethodSymbol m) =>
            Emit(KCheck.Of(
                NotNull(v),
                "CSV1014",
                a.Syntax,
                $"'{a.Value.Syntax}' might be null, but parameter '{a.Parameter.Name}' of '{m.Name}' is not nullable"));

        /// <summary>Does this collection member call its elements' Equals or GetHashCode, of a class of the program's that has its own?</summary>
        private static bool RunsEquals(IMethodSymbol callee)
        {
            if (!(callee.ContainingType is INamedTypeSymbol ct) || ct.TypeArguments.Length == 0 || !CustomEquality(ct.TypeArguments[0]))
            {
                return false;
            }
            var kind = CollectionKind(ct);
            var keyed = callee.OriginalDefinition.Parameters.Any(p => p.Type is ITypeParameterSymbol { Ordinal: 0 });
            return kind is "Dictionary" or "HashSet" ? keyed : callee.Name is "Contains" or "IndexOf" or "LastIndexOf" or "Remove" or "BinarySearch";
        }

        /// <summary>A delegate handed to a library member: the lambda it is, if it is one; whether it writes nothing; whether it accepts anything.</summary>
        private (IAnonymousFunctionOperation lambda, bool quiet, bool free) Handed(IArgumentOperation da)
        {
            var value = Unconverted(da.Value);
            var lambda = value is IDelegateCreationOperation dc ? LambdaOf(dc.Target) ?? LambdaBySymbol(dc.Target) : null;
            bool quiet = lambda != null && WritesNothing(lambda);
            bool free = lambda != null && _contractOf?.Invoke(lambda.Symbol) is Contract lc && lc.OwnRequires.Count == 0;
            return (lambda, quiet, free);
        }

        /// <summary>A library member whose stub contract the proof assumes.</summary>
        private void Assumed(IMethodSymbol m)
        {
            if (_p.Result != null && _contractOf?.Invoke(m) is Contract c && c.IsStub)
            {
                lock (_p.Result.Assumptions) _p.Result.Assumptions.Add(c.Method.ToDisplayString());
            }
        }

        /// <summary>
        /// A library member called as a procedure: a plain one (not a [Pure] stub's, which is a function), of a stub's
        /// contract or none (its result unknown), where the effects analysis says what it may write, of the subset's
        /// types, static or of a string, a library object or a token.
        /// </summary>
        private bool LibraryStub(IMethodSymbol m) =>
            PlainLibraryMember(m) && _contractOf?.Invoke(m) is Contract c && (c.IsStub && c.Stub != null && (c.Modifies == null || c.Stub.IsAsync) || !c.IsStub && !c.HasSource) && !c.IsTrusted &&
            KernelTypes.MayWriteHeap != null && KernelTypes.RunsUserCode != null &&
            m.Parameters.All(x => (x.RefKind == RefKind.None || x.RefKind == RefKind.Out && c.IsStub) && InSubset(x.Type)) && (m.ReturnsVoid || InSubset(m.ReturnType)) &&
            (m.IsStatic || IsString(m.ContainingType) || IsLibraryObject(m.ContainingType) || IsToken(m.ContainingType));

        /// <summary>A library's method or getter, not a collection's, not a [Pure] stub's, not generic, not async.</summary>
        private bool PlainLibraryMember(IMethodSymbol m) =>
            m.DeclaringSyntaxReferences.Length == 0 && !IsCollection(m.ContainingType) && !IsStub(m) && !m.IsGenericMethod && m.ContainingType is INamedTypeSymbol { IsGenericType: false } &&
            m.MethodKind is MethodKind.Ordinary or MethodKind.PropertyGet && !m.IsAsync;

        /// <summary>
        /// A library member without a stub: it may write the arrays it is handed (or the
        /// user code it runs does) where it may write memory at all (MayWriteHeap), any field where what it's handed
        /// may run the program's code or reach models (WritesFieldsAt), and nothing else; its ref and out arguments
        /// and its result are values not known (not null where they're declared so). Its receiver mustn't be null
        /// (CSV1013). Not where it is handed a delegate, where exceptions are seen, or cells are held.
        /// </summary>
        private (bool, KExpr) LibraryCall(IInvocationOperation call)
        {
            var outer = _cause;
            _cause = CallCause(call.TargetMethod) ?? outer;
            try
            {
                return LibraryCallCore(call);
            }
            finally
            {
                _cause = outer;
            }
        }

        private (bool, KExpr) LibraryCallCore(IInvocationOperation call)
        {
            var m = call.TargetMethod;
            if (m.DeclaringSyntaxReferences.Length > 0 || SpecSymbols.IsSpecClass(m.ContainingType) || m.ContainingNamespace?.ToDisplayString()?.StartsWith("CsVerify") == true ||
                KernelTypes.MayWriteHeap == null || KernelTypes.WritesFieldsAt == null || _p.Ghost || _contract.IsPure || _contract.IsLemma)
            {
                return (false, null);
            }
            // (a member with a stub is its stub's: Array.Fill, a list's)
            // (an async stub's, not awaited at once: the task is the library's, its contract of what it gives when awaited)
            bool asyncStub = KernelTypes.AsyncStub?.Invoke(m.OriginalDefinition) == true && !_awaiting;
            if (IsStub(m.OriginalDefinition) || !asyncStub && _contractOf?.Invoke(m) is Contract lc && (lc.IsStub || lc.IsPure))
            {
                return (false, null);
            }
            // (a delegate it's handed may run the program's code; one left at its default, null, runs nothing; a Func or an
            // Action: it must accept anything, and what it may change, changes)
            var handed = call.Arguments.Where(a => (a.Value.Type?.TypeKind == TypeKind.Delegate || a.Parameter?.Type.TypeKind == TypeKind.Delegate) &&
                                                   !(a.ArgumentKind == ArgumentKind.DefaultValue && a.Value.ConstantValue is { HasValue: true, Value: null })).ToList();
            // (one that runs it alongside, a thread pool's, a timer's, a task's continuation: it may run at any moment from
            // now on, so it may only be one that changes nothing, CSV1027; holding permissions, one too, CSV1016)
            bool alongside = handed.Count > 0 && (IsTaskLike(m.ReturnType) || m.ContainingNamespace?.ToDisplayString() is "System.Threading" or "System.Threading.Tasks" || m.ContainingType?.Name == "Timer");
            // (a lambda of a delegate type of the library's (WaitCallback, TimerCallback) handed to run alongside: whether it
            // writes is its own (its body is verified on its own); nothing else of it is the call's)
            var alongLambdas = alongside ? handed.Where(a => !IsFunc(a.Parameter.Type) && a.Parameter.RefKind == RefKind.None &&
                                                             Unconverted(a.Value) is IDelegateCreationOperation adc && LambdaOf(adc.Target) != null).ToList()
                                         : new List<IArgumentOperation>();
            handed = handed.Except(alongLambdas).ToList();
            // (a Func or an Action run alongside, Task.Run's: a task's, not a library call's)
            if (alongside && handed.Count > 0)
            {
                return (false, null);
            }
            if (handed.Any(a => !IsFunc(a.Parameter.Type) || a.Parameter.RefKind != RefKind.None))
            {
                return (false, null);
            }
            bool plain = handed.Count == 0 && ReachesOnlyArrays(call.Instance) && call.Arguments.All(a => a.ArgumentKind != ArgumentKind.Explicit || ReachesOnlyArrays(a.Value));
            if (!m.ReturnsVoid && !InSubset(m.ReturnType))
            {
                return (false, null);
            }
            // (a lock's object, a semaphore of a field, not null where it's declared so: a reference the kernel doesn't keep)
            bool lockObject = call.Instance is IFieldReferenceOperation { Field: var lof } && IsLockObject(lof) && NotNullable(lof.Type) && IsSemaphore(lof.Type) && m.Name == "Dispose";
            if (call.Instance != null && !lockObject && !(InSubset(call.Instance.Type) || IsLibraryObject(call.Instance.Type)))
            {
                return (false, null);
            }
            foreach (var a in call.Arguments.Where(a => a.ArgumentKind == ArgumentKind.Explicit && !alongLambdas.Contains(a)))
            {
                if (a.Parameter.RefKind != RefKind.Out && !InSubset(a.Value.Type) && !(a.Value is IConversionOperation { IsImplicit: true } ac && IsArray(ac.Operand.Type)) &&
                    !(a.Value is IInterpolatedStringOperation) && !IsQuoted(a.Value))
                {
                    return (false, null);
                }
            }
            foreach (var a in alongLambdas)
            {
                if (!WritesNothing(LambdaOf(((IDelegateCreationOperation)Unconverted(a.Value)).Target)))
                {
                    Emit(KCheck.Of(
                        KLit.False,
                        "CSV1027",
                        a.Syntax,
                        notAssumedAfter: true,
                        message: $"'{m.Name}' runs this alongside this code, at any moment from now on, and it writes: it may only be code that changes nothing"));
                }
            }
            // (the arrays it's handed, under cell permissions)
            var cellArrays = new List<(KExpr array, ITypeSymbol type)>();
            if (call.Instance != null && !lockObject)
            {
                var receiver = Expr(call.Instance);
                if (!m.IsStatic && !call.Instance.Type.IsValueType)
                {
                    Emit(KCheck.Of(NotNull(receiver), "CSV1013", call.Instance.Syntax, $"'{call.Instance.Syntax}' might be null in '{call.Syntax}'"));
                }
                if (IsArray(call.Instance.Type))
                {
                    cellArrays.Add((receiver, call.Instance.Type));
                }
            }
            // (an argument boxed or cast up to object for it: what it is, since the library's use of it isn't modeled)
            var delegates = new List<(IArgumentOperation arg, KExpr value)>();
            foreach (var a in call.Arguments.OrderBy(a => a.Parameter.Ordinal).Where(a => a.ArgumentKind == ArgumentKind.Explicit && a.Parameter.RefKind != RefKind.Out && !IsQuoted(a.Value) &&
                                                                                       (InSubset(a.Value.Type) || a.Value is IConversionOperation { IsImplicit: true } ac && IsArray(ac.Operand.Type))))
            {
                // (an array as System.Array: the array)
                var av = Expr(a.Value is IConversionOperation { IsImplicit: true } box && (box.Type.SpecialType == SpecialType.System_Object && InSubset(box.Operand.Type) || IsArray(box.Operand.Type) && !InSubset(box.Type)) ? box.Operand : a.Value);
                if (handed.Contains(a))
                {
                    delegates.Add((a, av));
                }
                if (IsArray(Unconverted(a.Value).Type))
                {
                    cellArrays.Add((av, Unconverted(a.Value).Type));
                }
                // (a parameter not nullable: the caller proves its argument isn't null, CSV1014)
                if (a.Parameter.RefKind == RefKind.None && IsNullable(a.Value.Type) && StaticChecks.IsNonNullable(a.Parameter))
                {
                    Emit(KCheck.Of(
                        NotNull(av),
                        "CSV1014",
                        a.Syntax,
                        (a.Value.ConstantValue is { HasValue: true, Value: null } ? "null is passed" : $"'{a.Value.Syntax}' might be null,") + $" but parameter '{a.Parameter.Name}' of '{m.Name}' is not nullable"));
                }
            }
            if (delegates.Count != handed.Count)
            {
                throw new NotTranslated("a delegate handed to " + m.Name + " that isn't a value");
            }
            bool delegatesQuiet = true;
            foreach (var (da, dv) in delegates)
            {
                var key = FuncKey(da.Parameter.Type);
                _p.DelegateKeys.Add(key);
                _p.CallsDelegates = true;
                var (lambda, quiet, free) = Handed(da);
                if (!free)
                {
                    Emit(KCheck.Of(
                        new KOp("$total." + key, dv),
                        "CSV1029",
                        da.Syntax,
                        lambda != null ? $"'{m.Name}' may call this with any arguments, but its precondition might not hold for them all"
                                                     : $"'{m.Name}' may call '{da.Value.Syntax}' with any arguments, but it isn't known to accept them all: say so with Spec.Requires(Spec.Total({da.Value.Syntax}))"));
                }
                if (_p.UsesPerm && !quiet)
                {
                    Emit(KCheck.Of(
                        new KOp("$nochange", dv),
                        "CSV1016",
                        da.Syntax,
                        $"'{m.Name}' calls '{da.Value.Syntax}', which may write anything, which this method's permissions don't allow (say it changes nothing with Spec.ChangesNothing)"));
                }
                else if (!quiet)
                {
                    delegatesQuiet = false;
                    _p.HavocsAll = true;
                    Emit(new KHavocAll { Unless = new KOp("$nochange", dv) });
                }
            }
            if (!delegatesQuiet)
            {
                ForgetCaptured();
            }
            ReentryUnderLock(m, call.Syntax);
            bool arrays = KernelTypes.MayWriteHeap(m), fields = KernelTypes.WritesFieldsAt(call);
            if (fields)
            {
                _p.HavocsAll = true;
                _p.CallsDelegates = true;
                Emit(new KHavocAll());
            }
            else if (arrays || cellArrays.Count > 0)
            {
                // (the arrays it may read or write: Checks's, which knows whether cells are held)
                var la = new KLibraryArrays
                {
                    Write = arrays,
                    Plain = plain,
                    At = call.Syntax,
                };
                if (arrays)
                {
                    foreach (var t in ElementTypes)
                    {
                        la.Fresh.Add((ElementMap(t), LinqMap("[Ref][int]" + ElementValue(t))));
                    }
                }
                foreach (var (array, type) in cellArrays)
                {
                    la.Arrays.Add((array, Elements(type), arrays ? LinqMap("[int]" + ElementValue(Elements(type))) : null));
                }
                Emit(la);
            }
            // (the library's nullability: a non-nullable out is not null, a [MaybeNullWhen(b)]
            // one not where it returns !b; a [NotNull] argument is not null after, a [NotNullWhen(b)] one where it returns b)
            var whenNotNull = new List<(KExpr value, bool when)>();
            foreach (var a in call.Arguments.Where(a => a.Parameter.RefKind is RefKind.Ref or RefKind.Out))
            {
                var v = RefVariable(a);
                Emit(KHavoc.Of(v));
                if (StaticChecks.IsNonNullable(a.Parameter) && IsNullable(a.Parameter.Type))
                {
                    Emit(KAssume.Of(NotNull(new KVar(v))));
                }
                else if (StaticChecks.NotNullWhen(a.Parameter) is bool when && IsNullable(a.Parameter.Type))
                {
                    whenNotNull.Add((new KVar(v), when));
                }
            }
            foreach (var a in call.Arguments.Where(a => a.Parameter != null && a.Parameter.RefKind == RefKind.None && IsNullable(a.Value.Type) && Unconverted(a.Value) is ILocalReferenceOperation or IParameterReferenceOperation))
            {
                foreach (var attr in a.Parameter.OriginalDefinition.GetAttributes())
                {
                    var name = attr.AttributeClass?.ToDisplayString();
                    var value = Expr(Unconverted(a.Value));
                    if (name == "System.Diagnostics.CodeAnalysis.NotNullAttribute")
                    {
                        Emit(KAssume.Of(NotNull(value)));
                    }
                    else if (name == "System.Diagnostics.CodeAnalysis.NotNullWhenAttribute" && m.ReturnType.SpecialType == SpecialType.System_Boolean &&
                             attr.ConstructorArguments.Length == 1 && attr.ConstructorArguments[0].Value is bool w)
                    {
                        whenNotNull.Add((value, w));
                    }
                }
            }
            // (where exceptions are seen: it may throw, anything, once it has done what it does)
            if (_cfgBlock != null && ThrowTarget(_cfgBlock.EnclosingRegion) is string throwsTo)
            {
                Emit(new KFork
                {
                    Overflow = KLit.False,
                    Target = throwsTo,
                    Exception = null,
                });
            }
            if (m.ReturnsVoid)
            {
                return (true, null);
            }
            var r = Declare("t$" + _temps++, call.Type);
            Emit(KHavoc.Of(r));
            // (a type parameter's, of a type argument not nullable: Dictionary<string, Item>'s GetOrAdd gives an Item)
            bool argumentNotNull = m.OriginalDefinition.ReturnType is ITypeParameterSymbol && NotNullable(m.ReturnType) &&
                                   !m.OriginalDefinition.GetReturnTypeAttributes().Any(a => a.AttributeClass?.Name == "MaybeNullAttribute");
            if (IsNullable(call.Type) && (StaticChecks.IsNonNullableReturn(m) || argumentNotNull))
            {
                Emit(KAssume.Of(NotNull(new KVar(r))));
            }
            foreach (var (value, when) in whenNotNull)
            {
                Emit(KAssume.Of(Implies(when ? new KVar(r) : Not(new KVar(r)), NotNull(value))));
            }
            return (true, new KVar(r));
        }

        // (a lambda quoted as an expression tree is data: EF's configuration, nothing that runs)
        private bool IsQuoted(IOperation v) => Unconverted(v) is IAnonymousFunctionOperation || v.Type is INamedTypeSymbol { Name: "Expression", Arity: 1 } && v.Type.ContainingNamespace?.ToDisplayString() == "System.Linq.Expressions";

        // (all it can reach is the arrays it's handed: no object of another kind, which under cell permissions it must be)
        private bool ReachesOnlyArrays(IOperation v) => v == null || v.ConstantValue.HasValue || Scalar(v.Type) || IsString(v.Type) || IsArray(Unconverted(v).Type);

        /// <summary>A stub's call: its receiver (not null) and arguments; its precondition checked, its value the function's.</summary>
        /// <summary>
        /// A collection's member with a [Pure] stub, of a value (List.IndexOf, Stack.Peek), as the collection's type is
        /// here (in a stub's own contract, its type parameters as this collection's): a function of the collection's models.
        /// </summary>
        private IMethodSymbol CollectionFunction(IMethodSymbol m)
        {
            if (m.ReturnsVoid || m.IsStatic || m.IsGenericMethod || !(m.ContainingType is INamedTypeSymbol t))
            {
                return null;
            }
            if (t.TypeArguments.Any(a => a is ITypeParameterSymbol))
            {
                var args = t.TypeArguments.Select(Actual).ToArray();
                if (args.Any(a => a is ITypeParameterSymbol))
                {
                    return null;
                }
                t = t.OriginalDefinition.Construct(args);
                m = t.GetMembers(m.Name).OfType<IMethodSymbol>().FirstOrDefault(x => SymbolEqualityComparer.Default.Equals(x.OriginalDefinition, m.OriginalDefinition));
                if (m == null)
                {
                    return null;
                }
            }
            if (!IsCollection(t) || !InSubset(m.ReturnType) || m.Parameters.Any(p => p.RefKind != RefKind.None || !InSubset(p.Type)))
            {
                return null;
            }
            return _contractOf?.Invoke(m) is Contract c && c.IsStub && c.IsPure && c.Stub != null ? m : null;
        }

        private KFnCall StubCall(IInvocationOperation call, Func<IOperation, KExpr> eval)
        {
            _p.Stubs.Add(call.TargetMethod.OriginalDefinition);
            var ordered = call.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => a.Value).ToList();
            KExpr receiver = null;
            KExpr[] args;
            if (eval == null)
            {
                var v = Operands((call.Instance == null ? new IOperation[0] : new[] { call.Instance }).Concat(ordered).ToArray());
                receiver = call.Instance == null ? null : v[0];
                args = call.Instance == null ? v : v.Skip(1).ToArray();
            }
            else
            {
                receiver = call.Instance == null ? null : eval(call.Instance);
                args = ordered.Select(eval).ToArray();
            }
            return new KFnCall
            {
                Callee = call.TargetMethod.OriginalDefinition,
                Receiver = receiver,
                ReceiverAt = call.Instance?.Syntax,
                Args = args,
                At = call.Syntax,
                Stub = true,
            };
        }

        private KExpr Call(IInvocationOperation call)
        {
            if (SpanExpr(call, Expr, inSpec: false) is KExpr span)
            {
                return span;
            }
            // (EF's change tracker: Lowering.EfTracker)
            var (tracker, trackerValue) = TrackerCall(call);
            if (tracker)
            {
                return trackerValue;
            }
            // (a lock wrapper's [Releases]: its gate given back, its invariants proved; [Acquires], not awaited: taken)
            var releasedGate = WrapperGate(call, acquiring: false);
            if (releasedGate != null)
            {
                Give(releasedGate, call.Syntax);
            }
            // (a library's lock wrapper, of a stub: taking or giving back its lock is all it does that the kernel knows of)
            if (call.TargetMethod.DeclaringSyntaxReferences.Length == 0 && (releasedGate != null || KernelTypes.Locks?.Acquires(call.TargetMethod) == true))
            {
                LockReceiver(call.Instance);
                if (!_awaiting && WrapperGate(call, acquiring: true) is IFieldSymbol libTaken)
                {
                    Take(libTaken, call.Syntax);
                }
                return null;
            }
            var value = CallCore(call);
            if (!_awaiting && WrapperGate(call, acquiring: true) is IFieldSymbol taken)
            {
                Take(taken, call.Syntax);
            }
            // (a call of the program's: what it may have done to a context, in this method's record)
            if (call.TargetMethod.DeclaringSyntaxReferences.Length > 0)
            {
                TrackerCallEffects(call.TargetMethod);
            }
            return value;
        }

        private KExpr CallCore(IInvocationOperation call)
        {
            // (EF's compiled query of a value: its query)
            if (CompiledQueryCall(call) is KExpr compiled)
            {
                return compiled;
            }
            // (a collection's member through IList or ICollection that changes it: by what the object is)
            if (IfcCall(call) is var (ifcHandled, ifcValue) && ifcHandled)
            {
                return ifcValue;
            }
            if (MemCall(call, out var memValue))
            {
                return memValue;
            }
            // (LINQ to Objects, read here: Lowering.Linq)
            if (IsEnumerableCall(call.TargetMethod) || IsQueryableMethod(call.TargetMethod) && call.Type is ITypeSymbol qt && !IsQueryHandle(qt))
            {
                _tableReads = null;
                return Linq(call);
            }
            // (a list's predicate methods, of a pure lambda: as LINQ's)
            if (call.Instance != null && IsList(call.Instance.Type) && call.Arguments.Length == 1 && call.TargetMethod.Name is "Find" or "FindIndex" or "Exists" or "TrueForAll" &&
                PureLambda(call.Arguments[0].Value) != null)
            {
                return ListPredicate(call);
            }
            // (an enumerator's MoveNext: the collection mustn't have changed since (its version), CSV1001; whether there's another, not known)
            if (call.TargetMethod.Name == "MoveNext" && call.Arguments.Length == 0 && call.Instance is ILocalReferenceOperation { Local: var el } && _enumerators.TryGetValue(el, out var ev))
            {
                var what = CollectionKind(ev.Type) switch { "Dictionary" => "dictionary", "HashSet" => "set", "Stack" => "stack", "Queue" => "queue", _ => "list" };
                Emit(KCheck.Of(
                    Eq(Sel(VersionMap, new KVar(ev.Of)), new KVar(ev.Version)),
                    "CSV1001",
                    call.Syntax,
                    $"the {what} may have changed while it is enumerated: MoveNext would throw InvalidOperationException (collection was modified)"));
                var more = Declare("t$" + _temps++, _model.Compilation.GetSpecialType(SpecialType.System_Boolean));
                Emit(KHavoc.Of(more));
                return new KVar(more);
            }
            // (waiting for a task started here: blocking, but not known to have finished it)
            if (call.TargetMethod.Name == "Wait" && call.Arguments.Length == 0 && call.Instance is ILocalReferenceOperation { Local: var wl } && _tasks.ContainsKey(wl))
            {
                return null;
            }
            // (waiting for a task one is given: a library call that changes nothing here)
            if (call.TargetMethod.Name == "Wait" && call.Arguments.Length == 0 && call.Instance != null && IsGivenTask(call.Instance.Type))
            {
                Expr(call.Instance);
                return null;
            }
            // (a delegate type's contract: its Invoke is a procedure of it alone, as an interface member is)
            if (call.TargetMethod.MethodKind == MethodKind.DelegateInvoke && Contracted(call.TargetMethod.ContainingType))
            {
                return Invoke(call.TargetMethod, call.Instance, call.Arguments, call.Syntax, null);
            }
            if (call.TargetMethod.MethodKind == MethodKind.DelegateInvoke)
            {
                return DelegateCall(call);
            }
            if (ElementwiseKind(call) != null)
            {
                return Elementwise(call);
            }
            // (a lock statement's Monitor.Enter and Monitor.Exit)
            if (call.TargetMethod.ContainingType?.ToDisplayString() == "System.Threading.Monitor" && call.TargetMethod.Name is "Enter" or "Exit")
            {
                Monitor(call);
                return null;
            }
            // (Monitor.Wait gives the lock back and takes it again: its invariants hold for the others, what it guards may
            // have changed meanwhile, and its invariants hold again; Pulse changes nothing here. Whether the lock is held,
            // and nothing else is, is StaticChecks', CSV1023 and CSV1025)
            if (call.TargetMethod.ContainingType?.ToDisplayString() == "System.Threading.Monitor" && call.TargetMethod.Name is "Wait" or "Pulse" or "PulseAll" && call.Arguments.Length > 0)
            {
                var ordered = call.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
                foreach (var a in ordered.Skip(1))
                {
                    if (InSubset(a.Value.Type))
                    {
                        Expr(a.Value);
                    }
                }
                if (call.TargetMethod.Name != "Wait")
                {
                    return null;
                }
                Waited(call);
                if (ordered.Count == 1)
                {
                    return KLit.True;
                }
                var pulsed = Declare("t$" + _temps++, call.TargetMethod.ReturnType);
                Emit(KHavoc.Of(pulsed));
                return new KVar(pulsed);
            }
            // (a try-lock's flag: taken by Interlocked where the if says it was free, given back in the finally)
            if (call.TargetMethod.ContainingType?.ToDisplayString() is "System.Threading.Interlocked" or "System.Threading.Volatile" && call.Arguments.Length > 0 &&
                FlagOf(call) is IFieldSymbol flag)
            {
                return FlagCall(call, flag);
            }
            // (Interlocked and Volatile of an atomic field: one step each)
            if (call.TargetMethod.ContainingType?.ToDisplayString() is "System.Threading.Interlocked" or "System.Threading.Volatile" && call.Arguments.Length > 0 &&
                call.Arguments.OrderBy(a => a.Parameter.Ordinal).First().Parameter.RefKind != RefKind.None)
            {
                return AtomicCall(call);
            }
            // (a lock primitive of this object's or a static one's: taking it forgets what it guards and gives its invariants;
            // giving it back proves them; its order is the static checks')
            if (Unconverted(call.Instance) is IFieldReferenceOperation { Field: IFieldSymbol pl } plr && IsLockPrimitive(pl.Type) && IsLockObject(pl) &&
                (pl.IsStatic || plr.Instance is IInstanceReferenceOperation))
            {
                foreach (var a in call.Arguments)
                {
                    if (InSubset(a.Value.Type) && a.Parameter.RefKind == RefKind.None)
                    {
                        Expr(a.Value);
                    }
                }
                var name = call.TargetMethod.Name;
                bool takes = name is "EnterReadLock" or "EnterWriteLock" or "EnterUpgradeableReadLock" or "WaitOne" or "Enter";
                bool gives = name is "ExitReadLock" or "ExitWriteLock" or "ExitUpgradeableReadLock" or "ReleaseMutex" or "Exit";
                if (!takes && !gives)
                {
                    throw new NotTranslated(name + " of a lock");
                }
                if (call.Arguments.Any(a => a.Parameter.RefKind != RefKind.None))
                {
                    throw new NotTranslated(name + " of a lock, with a variable it sets");
                }
                if (takes)
                {
                    Take(pl, call.Syntax);
                }
                else
                {
                    Give(pl, call.Syntax);
                }
                if (call.Type == null || call.Type.SpecialType == SpecialType.System_Void)
                {
                    return null;
                }
                var pr = Declare("t$" + _temps++, call.Type);
                Emit(KHavoc.Of(pr));
                return new KVar(pr);
            }
            // (in a lock wrapper itself, its semaphore is its callers' to hold)
            if (InWrapper && IsSemaphore(call.TargetMethod.ContainingType) && call.TargetMethod.Name is "Wait" or "Release" && call.Arguments.Length == 0)
            {
                if (call.Instance != null)
                {
                    Expr(Unconverted(call.Instance));
                }
                return null;
            }
            // (a lock wrapper's using ends: its gate is given back, its invariants proved)
            if (call.TargetMethod.ContainingType.ToDisplayString() == "System.IDisposable" && call.TargetMethod.Name == "Dispose" && KernelTypes.Locks != null &&
                UsingGate(call.Syntax) is IFieldSymbol usedGate)
            {
                Give(usedGate, call.Syntax);
                return null;
            }
            // (a gate: taken by Wait, given back by Release)
            if (IsSemaphore(call.TargetMethod.ContainingType) && call.TargetMethod.Name == "Wait" && call.Arguments.Length == 0)
            {
                if (GateOf(call) is IFieldSymbol wg)
                {
                    Take(wg, call.Syntax, _gateOwner);
                }
                return null;
            }
            if (IsSemaphore(call.TargetMethod.ContainingType) && call.TargetMethod.Name == "Release" && call.Arguments.Length == 0 &&
                Unconverted(call.Instance) is IFieldReferenceOperation { Field: IFieldSymbol plain } && GuardsNothing(plain))
            {
                return null;
            }
            if (IsSemaphore(call.TargetMethod.ContainingType) && call.TargetMethod.Name == "Release" && call.Arguments.Length == 0)
            {
                if (!(Unconverted(call.Instance) is IFieldReferenceOperation { Field: IFieldSymbol released } rf))
                {
                    throw new NotTranslated("a semaphore other than a gate");
                }
                KExpr relOwner = null;
                if (!released.IsStatic && !(rf.Instance is IInstanceReferenceOperation))
                {
                    if (!Fixed(rf.Instance))
                    {
                        throw new NotTranslated("a gate of an object that may change");
                    }
                    relOwner = Expr(rf.Instance);
                }
                Give(released, call.Syntax, of: relOwner);
                return null;
            }
            // (an async method's task is awaited at once, or it runs alongside: not yet)
            // (Task.Run(...) returned, or given on: it runs on, alongside the rest of this method, kept by whoever has it)
            if (!_awaiting && IsTaskRun(call, out var keptRun, out var keptLambda))
            {
                Detach(keptRun, keptLambda, kept: true);
                var kt = Declare("t$" + _temps++, call.Type);
                Emit(KHavoc.Of(kt));
                Emit(KAssume.Of(NotNull(new KVar(kt))));
                return new KVar(kt);
            }
            // (a task returned as it is made, return F(...) or a lambda's () => F(...): whoever has it awaits it)
            if (IsTaskMethod(call.TargetMethod) && !_awaiting &&
                (call.Syntax.Parent is ReturnStatementSyntax or ArrowExpressionClauseSyntax || call.Syntax.Parent is AnonymousFunctionExpressionSyntax af && af.ExpressionBody == call.Syntax))
            {
                return StartedTaskCall(call);
            }
            if (IsTaskMethod(call.TargetMethod) && !_awaiting)
            {
                throw new NotTranslated("a task that isn't awaited at once: " + call.TargetMethod.Name);
            }
            if (IsCollection(call.TargetMethod.ContainingType))
            {
                // (a builder's AppendFormat: its format checked, CSV1001)
                if (!_p.Ghost && !_contract.IsPure && !_contract.IsLemma && StaticChecks.FormatProblem(call) is var (cfat, cfmessage))
                {
                    Emit(KCheck.Of(KLit.False, "CSV1001", cfat, cfmessage));
                }
                return Invoke(call.TargetMethod, call.Instance, call.Arguments, call.Syntax, null);
            }
            // (IDisposable.Dispose of a class's object, as using calls it: that class's Dispose runs, its contract a
            // library interface's, so what it does isn't known: anything, as for a delegate)
            // (a library object's Dispose, as using calls it: the library's, which writes nothing of the program's)
            if (call.TargetMethod.ContainingType.ToDisplayString() == "System.IDisposable" && call.TargetMethod.Name == "Dispose" && call.Instance != null &&
                IsLibraryObject(Unconverted(call.Instance).Type) && !IsSemaphore(Unconverted(call.Instance).Type) && InSubset(Unconverted(call.Instance).Type))
            {
                Expr(Unconverted(call.Instance));
                return null;
            }
            if (call.TargetMethod.ContainingType.ToDisplayString() == "System.IDisposable" && call.TargetMethod.Name == "Dispose" && call.Instance != null &&
                IsClass(Unconverted(call.Instance).Type))
            {
                DelegatesHere("a call of Dispose");
                if (_cfgBlock != null && ThrowTarget(_cfgBlock.EnclosingRegion) != null)
                {
                    throw new NotTranslated("a call of Dispose where exceptions are seen");
                }
                Expr(Unconverted(call.Instance));
                _p.HavocsAll = true;
                _p.CallsDelegates = true;
                Emit(new KHavocAll());
                ForgetCaptured();
                return null;
            }
            var callee = call.TargetMethod.OriginalDefinition;
            if (StringEquals(call) is (IOperation ea, IOperation eb))
            {
                var v = Operands(ea, eb);
                if (call.Instance == null)
                {
                    return new KOp("streq", v[0], v[1]);
                }
                // (a.Equals(b) dereferences a: its length, read, is checked not null, and is never negative)
                var deref = new KLen
                {
                    String = true,
                    Array = v[0],
                    At = call.Syntax,
                    ArrayAt = call.Instance.Syntax,
                };
                return AndAlso(Ge(deref, KLit.Zero), new KOp("streq", v[0], v[1]));
            }
            // (a constant format string that would throw: CSV1001)
            if (!_p.Ghost && !_contract.IsPure && !_contract.IsLemma && StaticChecks.FormatProblem(call) is var (fat, fmessage))
            {
                Emit(KCheck.Of(KLit.False, "CSV1001", fat, fmessage));
            }
            // (Debug.Assert(c), Trace.Assert(c): c proved here, CSV1004, and known after; the message evaluated, not used)
            if (call.TargetMethod.Name == "Assert" && call.TargetMethod.IsStatic && call.TargetMethod.Parameters.Length >= 1 &&
                call.TargetMethod.Parameters[0].Type.SpecialType == SpecialType.System_Boolean &&
                call.TargetMethod.ContainingType?.ToDisplayString() is "System.Diagnostics.Debug" or "System.Diagnostics.Trace" && !_p.Ghost && !_contract.IsPure && !_contract.IsLemma)
            {
                var cond = call.Arguments.First(a => a.Parameter.Ordinal == 0).Value;
                var c = Expr(cond);
                foreach (var a in call.Arguments.Where(a => a.Parameter.Ordinal > 0 && a.ArgumentKind == ArgumentKind.Explicit).OrderBy(a => a.Parameter.Ordinal))
                {
                    if (InSubset(a.Value.Type))
                    {
                        Expr(a.Value);
                    }
                }
                Emit(KCheck.Of(c, "CSV1004", call.Syntax, $"'{call.TargetMethod.ContainingType.Name}.Assert({cond.Syntax})' might not hold"));
                return null;
            }
            // (a guard clause, ArgumentOutOfRangeException.ThrowIfNegative(i) and the rest: it may throw, and when it returns, what it checked holds)
            if (call.TargetMethod.ContainingType?.ToDisplayString() == "System.ArgumentOutOfRangeException" && call.TargetMethod.IsStatic &&
                call.TargetMethod.TypeArguments.Length == 1 && IsIntegral(call.TargetMethod.TypeArguments[0]) && GuardRelation(call.TargetMethod) is string rel)
            {
                var gm = call.TargetMethod;
                var ordered = call.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
                bool other = gm.Parameters.Length > 1 && SymbolEqualityComparer.Default.Equals(gm.Parameters[1].Type, gm.TypeArguments[0]);
                if (rel != "0" && !other)
                {
                    goto notGuard;
                }
                var v = Expr(ordered[0].Value);
                var o = other ? Expr(ordered[1].Value) : null;
                foreach (var a in ordered.Skip(other ? 2 : 1).Where(a => a.ArgumentKind == ArgumentKind.Explicit && InSubset(a.Value.Type)))
                {
                    Expr(a.Value);
                }
                if (_cfgBlock != null && ThrowTarget(_cfgBlock.EnclosingRegion) is string gt)
                {
                    Emit(new KFork
                    {
                        Overflow = KLit.False,
                        Target = gt,
                        Exception = null,
                    });
                }
                KExpr fact = gm.Name switch
                {
                    "ThrowIfNegative" => Ge(v, KLit.Zero),
                    "ThrowIfNegativeOrZero" => Gt(v, KLit.Zero),
                    "ThrowIfZero" => Ne(v, KLit.Zero),
                    _ => new KOp(rel, v, o),
                };
                Emit(KAssume.Of(fact));
                return null;
            }
            notGuard:
            if (!_isProcedure(callee) && IsStub(callee))
            {
                Assumed(callee);
                return StubCall(call, null);
            }
            // (a collection interface's Contains and IndexOf: of its elements, as the sequence they are)
            if (call.Instance != null && IsCollectionInterface(call.TargetMethod.ContainingType) && call.TargetMethod.Name is "Contains" or "IndexOf" && call.Arguments.Length == 1)
            {
                var src = Sequence(call.Instance);
                var x = Declare("t$" + _temps++, call.Arguments[0].Value.Type);
                Emit(KAssign.Of(x, Expr(call.Arguments[0].Value)));
                var has = new KQuantOver(this, KLit.Zero, src.Length, k => SameValue(src.Elem(k), new KVar(x), src.Type), forall: false).Q;
                var r = Declare("t$" + _temps++, call.Type);
                Emit(KHavoc.Of(r));
                KExpr fact;
                if (call.TargetMethod.Name == "Contains")
                {
                    fact = Eq(new KVar(r), has);
                }
                else
                {
                    var rv = new KVar(r);
                    var at = AndAlso(AndAlso(Le(KLit.Zero, rv), Lt(rv, src.Length)), SameValue(src.Elem(rv), new KVar(x), src.Type));
                    var first = new KQuantOver(this, KLit.Zero, rv, j => Not(SameValue(src.Elem(j), new KVar(x), src.Type)), forall: true).Q;
                    fact = OrElse(AndAlso(Eq(rv, KLit.MinusOne), Not(has)), AndAlso(at, first));
                }
                Emit(KSpecStmt.AssumedFree(fact, call.Syntax, argumentAt: call.Syntax));
                return new KVar(r);
            }
            // (a.GetLength(d) of a one-dimensional array: its length, d being 0, CSV1003)
            if (call.TargetMethod.Name == "GetLength" && call.TargetMethod.ContainingType?.SpecialType == SpecialType.System_Array && call.Instance != null &&
                Unconverted(call.Instance) is var gi && IsArray(gi.Type) && call.Arguments.Length == 1)
            {
                var v = Operands(gi, call.Arguments[0].Value);
                Emit(KCheck.Of(Eq(v[1], KLit.Zero), "CSV1003", call.Syntax, $"dimension in '{call.Syntax}' might be out of range"));
                return new KLen
                {
                    Array = v[0],
                    At = call.Syntax,
                    ArrayAt = gi.Syntax,
                };
            }
            // (Array.Fill(a, v), as its stub has it: a's elements all v, and nothing else changed)
            if (callee.ContainingType?.ToDisplayString() == "System.Array" && callee.Name == "Fill" && call.Arguments.Length == 2 &&
                call.Arguments.OrderBy(a => a.Parameter.Ordinal).First().Value is var fa && IsArray(fa.Type) && !_p.MemViews)
            {
                var ordered = call.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
                var v = Operands(ordered[0].Value, ordered[1].Value);
                if (NotNullable(ordered[0].Parameter.OriginalDefinition.Type))
                {
                    Emit(KCheck.Of(
                        NotNull(v[0]),
                        "CSV1014",
                        ordered[0].Syntax,
                        (ordered[0].Value.ConstantValue is { HasValue: true, Value: null } ? "null is passed" : $"'{ordered[0].Value.Syntax}' might be null,") +
                                      $" but parameter '{ordered[0].Parameter.Name}' of 'Fill' is not nullable"));
                }
                var map = Elements(fa.Type);
                var elem = ((IArrayTypeSymbol)fa.Type).ElementType;
                var row = LinqMap("[int]" + (IsRefArray(fa.Type) ? "Ref" : TypeOf(elem)));
                Emit(KRow.Of(map, v[0], new KVar(row), at: call.Syntax));
                Emit(KSpecStmt.AssumedFree(KQuant.ForAll("i$f", Eq(Sel(row, new KVar("i$f")), v[1])), call.Syntax, argumentAt: call.Syntax));
                return null;
            }
            if (callee.ContainingType?.ToDisplayString() == "System.Array" && !_p.MemViews && ArrayHelper(call) is var (helped, hv) && helped)
            {
                return hv;
            }
            if (!_isProcedure(callee) && LibraryCall(call) is var (handled, lib) && handled)
            {
                return lib;
            }
            // (as called: a generic one's instantiation boxes its arguments and unboxes its result)
            return Invoke(call.TargetMethod, call.Instance, call.Arguments, call.Syntax, null);
        }

        private KExpr Invoke(IMethodSymbol callee, IOperation instance, IReadOnlyList<IArgumentOperation> arguments, SyntaxNode at, KExpr value)
        {
            var outer = _cause;
            _cause = CallCause(callee) ?? outer;
            try
            {
                return InvokeCore(callee, instance, arguments, at, value);
            }
            finally
            {
                _cause = outer;
            }
        }

        private KExpr InvokeCore(IMethodSymbol callee, IOperation instance, IReadOnlyList<IArgumentOperation> arguments, SyntaxNode at, KExpr value)
        {
            // (a generic method's type arguments: references where its parameters are constrained to them)
            if (callee.IsGenericMethod && !callee.OriginalDefinition.TypeParameters.Zip(callee.TypeArguments).All(x => Instantiates(x.First, x.Second)))
            {
                throw new NotTranslated("a call of " + callee.Name + " with its type arguments");
            }
            // (a virtual [Pure] function called on an object made here: its class is known,
            // and that class's body answers: every write of the local an object of that class. A procedure is called
            // by the contract of the member as bound.)
            if ((callee.IsVirtual || callee.IsAbstract || callee.IsOverride) && !callee.ContainingType.IsSealed && _isFunction(callee.OriginalDefinition) &&
                Unconverted(instance) is ILocalReferenceOperation { Local: var recv } && MadeHere(recv) is var made && made.Count > 0)
            {
                var classes = made.Distinct<ITypeSymbol>(SymbolEqualityComparer.Default).ToList();
                if (classes.Count != 1 || classes[0] == null || !(Implementation(callee, (INamedTypeSymbol)classes[0]) is IMethodSymbol impl))
                {
                    throw new NotTranslated("a virtual call on an object made here");
                }
                callee = impl;
            }
            var constructed = callee;
            // (a list's member: the procedure of its stub, as it is for this list's kind)
            bool list = IsCollection(callee.ContainingType);
            bool listCtor = list && callee.MethodKind == MethodKind.Constructor || callee.MethodKind == MethodKind.Constructor && IsStruct(callee.ContainingType);
            if (list)
            {
                if (!(_contractOf?.Invoke(callee) is Contract lc && lc.IsStub))
                {
                    if (instance != null && !listCtor && callee.Parameters.All(p => p.RefKind == RefKind.None && InSubset(p.Type) && !IsDelegate(p.Type)) && (callee.ReturnsVoid || InSubset(callee.ReturnType)))
                    {
                        return CollectionUnstubbed(callee, instance, arguments, at);
                    }
                    throw new NotTranslated("a call of List's " + callee.Name + ", which has no stub contract");
                }
                // (a list of data values: its stubs compare elements as references, which data values aren't)
                if (((INamedTypeSymbol)callee.ContainingType).TypeArguments.Any(IsData) && callee.Name is "Contains" or "IndexOf" or "LastIndexOf" or "Remove" or "BinarySearch")
                {
                    throw new NotTranslated("a list of data values' " + callee.Name);
                }
                // (of objects: their own Equals, any type's, which a reference's comparison isn't)
                if (((INamedTypeSymbol)callee.ContainingType).TypeArguments.Any(a => a.SpecialType == SpecialType.System_Object) && callee.Name is "Contains" or "IndexOf" or "LastIndexOf" or "Remove" or "BinarySearch")
                {
                    throw new NotTranslated("a list of objects' " + callee.Name);
                }
                if (_p.UsesPerm)
                {
                    throw new NotTranslated("a list with permissions");
                }
                _p.LibCalls.Add(callee);
                foreach (var model in ModelsOf((INamedTypeSymbol)callee.ContainingType))
                {
                    _p.Models[model.Name] = model;
                }
            }
            else
            {
                callee = callee.OriginalDefinition;
            }
            // (a library member with a stub contract that writes nothing: a procedure of its contract)
            bool lib = !list && LibraryStub(callee);
            if (lib)
            {
                _p.LibCalls.Add(callee);
            }
            if (list || lib)
            {
                Assumed(callee);
            }
            if (!list && !lib && !_isProcedure(callee))
            {
                throw new NotTranslated("a call of " + callee.Name);
            }
            UnderLock(callee, at, instance, arguments);
            ReentryUnderLock(callee, at);
            _p.Calls.Add(callee);
            var ordered = arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
            // (a local function's: what it captures, passed after its arguments, as they are here; and this, where it has it)
            var localCaptures = callee.MethodKind == MethodKind.LocalFunction ? LocalFunctionCaptures(callee) : null;
            bool localThis = localCaptures != null && !StaticContext(callee);
            if (!callee.IsStatic && instance == null && !listCtor && localCaptures == null)
            {
                throw new NotTranslated("a call of " + callee.Name + " without its receiver");
            }
            var call = (Instance: instance, Syntax: at);
            bool onThis = call.Instance is IInstanceReferenceOperation || localThis;
            // (a ref or out argument is a variable, which gets what the callee gives back; an out one isn't read)
            var refOuts = ordered.Where(a => a.Parameter.RefKind is RefKind.Ref or RefKind.Out).Select(a => (a.Parameter.Ordinal, RefVariable(a))).ToList();
            // (two arguments by reference, one written, must not be the same: the callee's parameters are variables of their
            // own (CSV1020); a linear value given twice is the analyzer's, CSV0007)
            for (int i = 0; i < refOuts.Count; i++)
            {
                for (int j = i + 1; j < refOuts.Count; j++)
                {
                    var (x, y) = (ordered.First(o => o.Parameter.Ordinal == refOuts[i].Ordinal), ordered.First(o => o.Parameter.Ordinal == refOuts[j].Ordinal));
                    if (x.Value is IDiscardOperation || y.Value is IDiscardOperation)
                    {
                        continue;
                    }
                    var message = $"'{x.Value.Syntax}' and '{y.Value.Syntax}' might be the same {{0}}, passed by reference to two parameters of '{callee.Name}'";
                    if (_lentCells.TryGetValue(refOuts[i].Item2, out var cx) && _lentCells.TryGetValue(refOuts[j].Item2, out var cy))
                    {
                        Emit(KCheck.Of(OrElse(Ne(cx.array, cy.array), Ne(cx.index, cy.index)), "CSV1020", at, string.Format(message, "array cell")));
                    }
                    else if (refOuts[i].Item2 == refOuts[j].Item2)
                    {
                        // (a view, or a package of them, given twice: the analyzer's linearity error (CSV0007); its permissions
                        // twice, nothing to go on with)
                        if (IsView(x.Parameter.Type) || IsMemView(x.Parameter.Type) || IsPackage(x.Parameter.Type))
                        {
                            Emit(KAssume.Of(KLit.False));
                        }
                        else
                        {
                            Emit(KCheck.Of(KLit.False, "CSV1020", at, string.Format(message, "variable"), notAssumedAfter: true));
                        }
                        // (a copy for the second, as Boogie can't give one variable twice)
                        var copy = Declare("t$" + _temps++, y.Parameter.Type);
                        Emit(KAssign.Of(copy, new KVar(refOuts[j].Item2)));
                        refOuts[j] = (refOuts[j].Ordinal, copy);
                    }
                }
            }
            var ins = ordered.Where(a => a.Parameter.RefKind != RefKind.Out).ToList();
            // (an in argument of a value: its value; of a cell the callee may write, not translated)
            // (a local, a parameter, or an array's cell the callee doesn't touch arrays besides; a
            // struct's member isn't translated; anything else is not supported, CSV1901)
            bool cellReported = false;
            foreach (var ia in ins.Where(a => a.Parameter.RefKind == RefKind.In && InValue(a.Parameter) && a.ArgumentKind == ArgumentKind.Explicit))
            {
                switch (Unconverted(ia.Value))
                {
                    case ILocalReferenceOperation or IParameterReferenceOperation: break;
                    case IArrayElementReferenceOperation:
                        if (!cellReported && (KernelTypes.MayWriteHeap == null || KernelTypes.MayWriteHeap(callee.OriginalDefinition)))
                        {
                            Emit(KCheck.Of(
                                KLit.False,
                                "CSV1901",
                                ia.Syntax,
                                notAssumedAfter: true,
                                message: $"passing '{ia.Value.Syntax}' by reference to '{callee.Name}', which may write array contents itself, is not supported: the cell and the parameter would disagree (copy the element into a local)"));
                        }
                        cellReported = true;
                        break;
                    case var other when StructMember(other) is not null: throw new NotTranslated("a struct's member given by in");
                    default:
                        Emit(KCheck.Of(
                            KLit.False,
                            "CSV1901",
                            ia.Syntax,
                            notAssumedAfter: true,
                            message: $"passing '{ia.Value.Syntax}' by in is not supported: only locals, parameters, array elements and their structs' members"));
                        break;
                }
            }
            var operands = (call.Instance == null || onThis ? Enumerable.Empty<IOperation>() : new[] { call.Instance }).Concat(ins.Select(a => a.Value)).ToArray();
            var values = Operands(operands);
            var receiver = localThis ? new KVar("this") : call.Instance == null ? null : onThis ? Expr(call.Instance) : values[0];
            var inValues = call.Instance == null || onThis ? values : values.Skip(1).ToArray();
            var args = new KExpr[ordered.Count + (value == null ? 0 : 1)];
            for (int k = 0; k < ins.Count; k++)
            {
                var ordinal = ins[k].Parameter.Ordinal;
                // (a collection's key, of a dictionary or a set: as it compares them; a list's elements are what they are)
                args[ordinal] = list ? (CustomEquality(ins[k].Parameter.Type) && !(CollectionKind(callee.ContainingType) is "Dictionary" or "HashSet" &&
                                                                                   callee.OriginalDefinition.Parameters[ordinal].Type is ITypeParameterSymbol { Ordinal: 0 })
                                        ? inValues[k] : Keyed(inValues[k], ins[k].Parameter.Type)) : Box(inValues[k], callee.OriginalDefinition.Parameters[ordinal].Type, ins[k].Parameter.Type);
            }
            if (value != null)
            {
                args[ordered.Count] = list ? value : Box(value, callee.OriginalDefinition.Parameters.Last().Type, constructed.Parameters.Last().Type);
            }
            foreach (var (ordinal, v) in refOuts)
            {
                args[ordinal] ??= new KVar(v);
            }
            // (a variable the flow graph captured: its value at the call, which an argument after it may have changed)
            foreach (var (ordinal, v) in refOuts)
            {
                if (ordered.First(a => a.Parameter.Ordinal == ordinal).Value is IFlowCaptureReferenceOperation rc && _captured.TryGetValue(rc.Id, out var rcv) &&
                    rcv is ILocalReferenceOperation or IParameterReferenceOperation)
                {
                    args[ordinal] = new KVar(v);
                }
            }
            if (lib)
            {
                HandedToLibrary(callee, ordered, args);
            }
            var argsAt = ordered.Select(a => a.Value.Syntax).Concat(value == null ? new SyntaxNode[0] : new[] { at }).ToArray();
            if (localCaptures != null && localCaptures.Count > 0)
            {
                args = args.Concat(localCaptures).ToArray();
                argsAt = argsAt.Concat(localCaptures.Select(_ => at)).ToArray();
            }
            var gives = Returns(constructed);
            var result = listCtor ? Declare("t$" + _temps++, callee.ContainingType) : gives == null ? null : Declare("t$" + _temps++, !list && Returns(callee.OriginalDefinition) is ITypeParameterSymbol tp ? tp : gives);
            // (where exceptions are seen, a call of what may throw (not a proof) throws, or returns)
            var throwsTo = _cfgBlock == null || _contractOf?.Invoke(callee) is Contract cc && (cc.IsPure || cc.IsLemma) ? null : ThrowTarget(_cfgBlock.EnclosingRegion);
            SteadyArguments(callee, args, call.Syntax);
            // (an async callee's awaits let other code run, which can't reach this method's confined objects)
            var keepers = IsTaskMethod(constructed) && !list ? Confined().Select(l => Declare(Local(l), l.Type)).ToList() : new List<string>();
            int keepId = _keeps++;
            if (keepers.Count > 0)
            {
                Emit(new KKeep
                {
                    Id = keepId,
                    Keep = keepers,
                });
            }
            // (a struct's method that writes this: the receiver's new value, written back where it is; on this, this)
            string thisOut = null;
            if (WritesStructThis(callee))
            {
                if (_phase != 0)
                {
                    throw new NotTranslated("a struct's method that writes this, run alongside");
                }
                if (onThis && !_p.StructThis)
                {
                    throw new NotTranslated("a struct's method that writes this, called on this where this isn't written");
                }
                if (onThis)
                {
                    thisOut = "this";
                }
                else
                {
                    thisOut = Declare("t$" + _temps++, call.Instance.Type);
                    var where = Unconverted(call.Instance) is IFlowCaptureReferenceOperation ic && _captured.TryGetValue(ic.Id, out var icv) ? icv : call.Instance;
                    if (where is ILocalReferenceOperation or IParameterReferenceOperation or IFieldReferenceOperation or IArrayElementReferenceOperation || StructMember(where) != null)
                    {
                        _writeBacks.Add((where, thisOut));
                    }
                }
            }
            Emit(new KCall
            {
                Callee = callee,
                Receiver = receiver,
                ReceiverIsThis = onThis,
                ReceiverAt = call.Instance?.Syntax,
                ThrowsTo = _phase == 1 ? null : throwsTo,
                Phase = _phase,
                Args = args,
                ArgsAt = argsAt,
                Result = result,
                ThisOut = thisOut,
                At = call.Syntax,
                RefOuts = refOuts,
            });
            // (a collection that compares its elements with an Equals of the program's, or hashes them: that code runs, and
            // may change anything)
            if (list && RunsEquals(callee))
            {
                _p.HavocsAll = true;
                _p.CallsDelegates = true;
                Emit(new KHavocAll { ProgramState = true });
            }
            // (the cells and struct members lent: what the callee gave back, written where they are)
            var writeBacks = _writeBacks.ToList();
            _writeBacks.Clear();
            foreach (var (target, var) in writeBacks)
            {
                Assign(target, new KVar(var));
            }
            if (keepers.Count > 0)
            {
                Emit(new KKeep
                {
                    Id = keepId,
                    After = true,
                    Keep = keepers,
                });
            }
            if (!(_contractOf?.Invoke(callee) is Contract pc && (pc.IsPure || pc.IsLemma)))
            {
                ForgetCaptured();
            }
            foreach (var (_, rv) in refOuts)
            {
                var ro = ordered.FirstOrDefault(a => RefVariableName(a) == rv);
                if (ro != null && HasInvariants(ro.Parameter.Type))
                {
                    AssumeValid(new KVar(rv), ro.Parameter.Type);
                }
            }
            // (the views it gives back, or lent it in, say what their cells hold now)
            foreach (var (ordinal, rv) in refOuts)
            {
                if (IsMemView(callee.Parameters[ordinal].Type))
                {
                    Emit(KAssume.Of(MemTie(new KVar(rv), callee.Parameters[ordinal].Type)));
                    MemLive(new KVar(rv), callee.Parameters[ordinal].Type, at, true);
                }
            }
            for (int k = 0; k < ins.Count; k++)
            {
                if (ins[k].Parameter.RefKind == RefKind.In && IsMemView(ins[k].Parameter.Type))
                {
                    Emit(KAssume.Of(MemTie(inValues[k], ins[k].Parameter.Type)));
                }
            }
            if (result != null && gives != null && IsMemView(gives))
            {
                Emit(KAssume.Of(MemTie(new KVar(result), gives)));
            }
            if (result == null)
            {
                return null;
            }
            if (gives != null && HasInvariants(gives))
            {
                AssumeValid(new KVar(result), gives);
            }
            return list || gives == null ? new KVar(result) : Unbox(new KVar(result), Returns(callee.OriginalDefinition), gives);
        }

        /// <summary>
        /// The classes of the objects a local is given, where some write of it makes one (new C(...)): each write's (null
        /// for one that isn't a new object), in the method and its lambdas, by ref and out too. Empty where none is new.
        /// </summary>
        private List<ITypeSymbol> MadeHere(ILocalSymbol local)
        {
            var writes = new List<ExpressionSyntax>();
            foreach (var n in _decl.DescendantNodes())
            {
                switch (n)
                {
                    case VariableDeclaratorSyntax v when v.Initializer != null && SymbolEqualityComparer.Default.Equals(_model.GetDeclaredSymbol(v), local):
                        writes.Add(v.Initializer.Value);
                        break;
                    case AssignmentExpressionSyntax asg when SymbolEqualityComparer.Default.Equals(_model.GetSymbolInfo(asg.Left).Symbol, local):
                        writes.Add(asg.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.SimpleAssignmentExpression) ? asg.Right : null);
                        break;
                    case ArgumentSyntax arg when !arg.RefKindKeyword.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.None) && arg.Expression is IdentifierNameSyntax or DeclarationExpressionSyntax &&
                                                 SymbolEqualityComparer.Default.Equals(arg.Expression is DeclarationExpressionSyntax { Designation: SingleVariableDesignationSyntax d } ? _model.GetDeclaredSymbol(d) : _model.GetSymbolInfo(arg.Expression).Symbol, local):
                        writes.Add(null); break;
                }
            }
            if (!writes.Any(w => w != null && Unwrapped(w) is BaseObjectCreationExpressionSyntax))
            {
                return new List<ITypeSymbol>();
            }
            return writes.Select(w => w != null && Unwrapped(w) is BaseObjectCreationExpressionSyntax oc ? _model.GetTypeInfo(oc).Type : null).ToList();
        }

        private ExpressionSyntax Unwrapped(ExpressionSyntax e) => e is ParenthesizedExpressionSyntax p ? Unwrapped(p.Expression) : e is CastExpressionSyntax c ? Unwrapped(c.Expression) : e;

        /// <summary>The method that runs for a call of m on an object whose class is c: m's override in c or its nearest base, or c's implementation of an interface's m.</summary>
        private static IMethodSymbol Implementation(IMethodSymbol m, INamedTypeSymbol c)
        {
            var def = m.OriginalDefinition;
            if (def.ContainingType.TypeKind == TypeKind.Interface)
            {
                return c.FindImplementationForInterfaceMember(def) as IMethodSymbol;
            }
            for (var t = c; t != null; t = t.BaseType)
            {
                foreach (var x in t.GetMembers(def.Name).OfType<IMethodSymbol>())
                {
                    for (var o = x; o != null; o = o.OverriddenMethod)
                    {
                        if (SymbolEqualityComparer.Default.Equals(o.OriginalDefinition, def))
                        {
                            return x.IsAbstract ? null : x;
                        }
                    }
                }
            }
            return null;
        }
    }
}
