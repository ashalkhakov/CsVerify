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
    /// <summary>foreach: over arrays and strings by index, collections by their models or enumerators, any IEnumerable; iterators.</summary>
    internal sealed partial class Lowering
    {
        /// <summary>An iterator's caller runs (before its first MoveNext, and between the next): anything may change.</summary>
        private void CallersRun()
        {
            _p.HavocsAll = true;
            _p.CallsDelegates = true;
            Emit(new KHavocAll());
        }

        // ------------------------------------------------------------------ foreach

        /// <summary>A foreach over an array or a string, as C# compiles it: an index from 0 to its length.</summary>
        private sealed class ForEach
        {
            public int Head;
            public string Array, Index;
            public ITypeSymbol Type, Element;
            public bool String;
            /// <summary>Over a collection (null: an array or a string).</summary>
            public INamedTypeSymbol Collection;
            /// <summary>A list its loop may change: through its enumerator, whose MoveNext checks the list's version (Version, as it was).</summary>
            public string Version;
            /// <summary>Through an enumerator: the collection's Count where the loop began.</summary>
            public string Size0;
            /// <summary>An IEnumerable the kernel doesn't look into (Of, the sequence): its MoveNext may change anything.</summary>
            public bool Opaque;
            /// <summary>A dictionary's Keys or Values (null: the collection itself), enumerated as the dictionary is; Of, the dictionary.</summary>
            public string View;
            public IOperation Of;
            /// <summary>A LINQ query's (or a group's): what's read where the loop starts (Query, or the group of GroupOf's
            /// variable), into the map Mat of Count elements.</summary>
            public IOperation Query;
            public ILocalSymbol GroupOf;
            /// <summary>A GroupJoin's group of a row (the loop over row.os): the row's variable.</summary>
            public ILocalSymbol JoinGroupOf;
            public string Mat, Count;
            public SyntaxNode At;
        }

        private readonly Dictionary<CaptureId, ForEach> _forEach = new Dictionary<CaptureId, ForEach>();
        private readonly Dictionary<int, ForEach> _forEachAt = new Dictionary<int, ForEach>();
        private readonly Dictionary<ILocalSymbol, ForEach> _forEachOf = new Dictionary<ILocalSymbol, ForEach>(SymbolEqualityComparer.Default);
        /// <summary>The try/finally regions of those loops' enumerators: C# emits neither.</summary>
        private readonly HashSet<ControlFlowRegion> _erased = new HashSet<ControlFlowRegion>();

        private void ForEachLoops(ControlFlowGraph cfg)
        {
            foreach (var fs in _decl.DescendantNodes().OfType<CommonForEachStatementSyntax>())
            {
                if (!(_model.GetOperation(fs) is IForEachLoopOperation fo))
                {
                    continue;
                }
                if (fo.IsAsynchronous)
                {
                    AsyncForEach(fs, fo, cfg);
                    continue;
                }
                var collection = Unconverted(fo.Collection);
                // (a dictionary's Keys or Values: a view of it, enumerated through the dictionary's enumerator, its version checked)
                string view = null;
                if (collection is IPropertyReferenceOperation { Property.Name: "Keys" or "Values" } kv && kv.Instance != null && CollectionKind(kv.Instance.Type) == "Dictionary" && IsCollection(kv.Instance.Type))
                {
                    view = kv.Property.Name;
                    collection = Unconverted(kv.Instance);
                }
                bool isString = IsString(collection.Type);
                bool isCollection = IsCollection(collection.Type);
                // (a LINQ query, or one of its groups: read into a map where the loop starts, then indexed)
                if (!IsArray(collection.Type) && !isString && !isCollection && QueryForEach(fs, fo, cfg, collection))
                {
                    continue;
                }
                // (any other IEnumerable<T>, an iterator's say: an enumerator whose MoveNext may run the program's code,
                // whose contract (the library interface's) says nothing)
                if (!IsArray(collection.Type) && !isString && !isCollection && IsSequence(collection.Type))
                {
                    OpaqueForEach(fs, fo, cfg, collection);
                    continue;
                }
                if (!IsArray(collection.Type) && !isString && !isCollection)
                {
                    continue;
                }
                // (a list: over its model, where the loop changes no list; any other collection, or a list it may change,
                // through its enumerator, whose MoveNext checks the collection's version)
                bool enumerated = isCollection && !(IsList(collection.Type) && ChangesNoList(fs.Statement));
                bool pairs = CollectionKind(collection.Type) == "Dictionary" && view == null;
                var element = view != null ? ((INamedTypeSymbol)collection.Type).TypeArguments[view == "Keys" ? 0 : 1]
                            : isString ? _model.Compilation.GetSpecialType(SpecialType.System_Char)
                            : pairs ? fo.Locals.FirstOrDefault()?.Type ?? throw new NotTranslated("a foreach over a dictionary without its variable")
                            : isCollection ? ((INamedTypeSymbol)collection.Type).TypeArguments[0] : ((IArrayTypeSymbol)collection.Type).ElementType;
                if (pairs && !IsPair(element))
                {
                    throw new NotTranslated("a foreach over a dictionary not by its pairs");
                }
                var conv = Microsoft.CodeAnalysis.CSharp.CSharpExtensions.GetForEachStatementInfo(_model, fs).ElementConversion;
                var target = fo.Locals.FirstOrDefault()?.Type;
                if (!(conv.IsIdentity || conv.IsImplicit && conv.IsNumeric && IsIntegral(element) && target != null && IsIntegral(target)))
                {
                    throw new NotTranslated("a foreach's conversion of its elements");
                }
                var capture = cfg.Blocks.SelectMany(b => b.Operations).OfType<IFlowCaptureOperation>()
                    .FirstOrDefault(c => c.Syntax == fs.Expression && c.Value is IInvocationOperation gi && gi.TargetMethod.Name == "GetEnumerator");
                var head = capture == null ? null : cfg.Blocks.FirstOrDefault(b => b.BranchValue is IInvocationOperation mn && mn.TargetMethod.Name == "MoveNext" &&
                                                                                   mn.Instance is IFlowCaptureReferenceOperation r && r.Id.Equals(capture.Id));
                if (head == null)
                {
                    throw new NotTranslated("a foreach without its enumerator");
                }
                var n = _forEachAt.Count;
                var fe = new ForEach
                {
                    Head = head.Ordinal,
                    Array = Declare($"fe${n}$a", collection.Type),
                    Index = Declare($"fe${n}$i", _model.Compilation.GetSpecialType(SpecialType.System_Int32)),
                    Type = collection.Type,
                    Element = element,
                    String = isString,
                    At = fs.Expression,
                    Collection = isCollection ? (INamedTypeSymbol)collection.Type : null,
                    View = view,
                    Of = view != null ? collection : null,
                };
                if (isCollection)
                {
                    foreach (var model in ModelsOf(fe.Collection))
                    {
                        _p.Models[model.Name] = model;
                    }
                }
                if (enumerated)
                {
                    fe.Version = Declare($"fe${n}$v", _model.Compilation.GetSpecialType(SpecialType.System_Int32));
                }
                if (enumerated && ModelOf("Size", fe.Collection) != null)
                {
                    fe.Size0 = Declare($"fe${n}$c", _model.Compilation.GetSpecialType(SpecialType.System_Int32));
                }
                _forEach[capture.Id] = fe;
                _forEachAt[head.Ordinal] = fe;
                foreach (var l in fo.Locals)
                {
                    _forEachOf[l] = fe;
                }
                for (var region = head.EnclosingRegion; region != null; region = region.EnclosingRegion)
                {
                    if (region.Kind == ControlFlowRegionKind.Try && region.EnclosingRegion?.Kind == ControlFlowRegionKind.TryAndFinally)
                    {
                        _erased.Add(region.EnclosingRegion);
                        break;
                    }
                }
            }
        }

        /// <summary>
        /// foreach over an IEnumerable&lt;T&gt; the kernel doesn't look into (an iterator's): the sequence evaluated once (a
        /// null one throws), each MoveNext code that may change anything and whose answer isn't known, each element a
        /// value of its type; Spec.Index counts the edges back to the head.
        /// </summary>
        private void OpaqueForEach(CommonForEachStatementSyntax fs, IForEachLoopOperation fo, ControlFlowGraph cfg, IOperation collection)
        {
            var element = ((INamedTypeSymbol)collection.Type).TypeArguments[0];
            var target = fo.Locals.FirstOrDefault()?.Type;
            if (target != null && !SymbolEqualityComparer.Default.Equals(target, element))
            {
                throw new NotTranslated("a foreach's conversion of its elements");
            }
            // (its expression, or within it: xs!'s is xs's)
            var capture = cfg.Blocks.SelectMany(b => b.Operations).OfType<IFlowCaptureOperation>()
                .FirstOrDefault(c => fs.Expression.DescendantNodesAndSelf().Contains(c.Syntax) && c.Value is IInvocationOperation gi && gi.TargetMethod.Name == "GetEnumerator");
            var head = capture == null ? null : cfg.Blocks.FirstOrDefault(b => b.BranchValue is IInvocationOperation mn && mn.TargetMethod.Name == "MoveNext" &&
                                                                               mn.Instance is IFlowCaptureReferenceOperation r && r.Id.Equals(capture.Id));
            if (head == null)
            {
                throw new NotTranslated("a foreach without its enumerator");
            }
            var n = _forEachAt.Count;
            var fe = new ForEach
            {
                Head = head.Ordinal,
                Array = Declare($"fe${n}$a", collection.Type),
                Index = Declare($"fe${n}$i", _model.Compilation.GetSpecialType(SpecialType.System_Int32)),
                Type = collection.Type,
                Element = element,
                At = fs.Expression,
                Opaque = true,
                Of = collection,
            };
            _forEach[capture.Id] = fe;
            _forEachAt[head.Ordinal] = fe;
            foreach (var l in fo.Locals)
            {
                _forEachOf[l] = fe;
            }
            for (var region = head.EnclosingRegion; region != null; region = region.EnclosingRegion)
            {
                if (region.Kind == ControlFlowRegionKind.Try && region.EnclosingRegion?.Kind == ControlFlowRegionKind.TryAndFinally)
                {
                    _erased.Add(region.EnclosingRegion);
                    break;
                }
            }
        }

        /// <summary>Explicit enumerators of collections, by their locals: the collection, its version where it was made.</summary>
        private readonly Dictionary<ILocalSymbol, (string Of, string Version, INamedTypeSymbol Type)> _enumerators = new Dictionary<ILocalSymbol, (string, string, INamedTypeSymbol)>(SymbolEqualityComparer.Default);

        /// <summary>await foreach's enumerators, by their captures: the element type, and where the loop's collection is.</summary>
        private readonly Dictionary<CaptureId, (ITypeSymbol Element, SyntaxNode At)> _asyncEach = new Dictionary<CaptureId, (ITypeSymbol, SyntaxNode)>();

        /// <summary>
        /// await foreach over a library's async stream (a channel's ReadAllAsync): each round awaits, as any await does,
        /// and may throw; whether there is another, and what it is, isn't known (not null where its type says so).
        /// The enumerator's DisposeAsync, in the finally C# emits, is left out.
        /// </summary>
        private void AsyncForEach(CommonForEachStatementSyntax fs, IForEachLoopOperation fo, ControlFlowGraph cfg)
        {
            var capture = cfg.Blocks.SelectMany(b => b.Operations).OfType<IFlowCaptureOperation>()
                .FirstOrDefault(c => c.Syntax == fs.Expression && c.Value is IInvocationOperation gi && gi.TargetMethod.Name == "GetAsyncEnumerator");
            if (capture == null)
            {
                throw new NotTranslated("an await foreach without its enumerator");
            }
            var info = Microsoft.CodeAnalysis.CSharp.CSharpExtensions.GetForEachStatementInfo(_model, fs);
            if (!info.ElementConversion.IsIdentity || !InSubset(info.ElementType))
            {
                throw new NotTranslated("an await foreach of " + info.ElementType);
            }
            // (the element as the stream's type has it, nullability and all: a ConfigureAwait's view loses it)
            var element = info.ElementType;
            var src = Unconverted(((IInvocationOperation)capture.Value).Instance ?? ((IInvocationOperation)capture.Value).Arguments.FirstOrDefault()?.Value);
            while (src is IInvocationOperation c && c.TargetMethod.Name is "ConfigureAwait" or "WithCancellation")
            {
                src = Unconverted(c.Instance ?? c.Arguments.First(a => a.Parameter.Ordinal == 0).Value);
            }
            if (src?.Type is INamedTypeSymbol { Name: "IAsyncEnumerable", Arity: 1 } st && SymbolEqualityComparer.Default.Equals(st.TypeArguments[0], element))
            {
                element = st.TypeArguments[0];
            }
            _asyncEach[capture.Id] = (element, fs.Expression);
            var head = cfg.Blocks.FirstOrDefault(b => b.BranchValue != null && b.BranchValue.DescendantsAndSelf().OfType<IInvocationOperation>()
                .Any(mn => mn.TargetMethod.Name == "MoveNextAsync" && mn.Instance is IFlowCaptureReferenceOperation r && r.Id.Equals(capture.Id)));
            for (var region = head?.EnclosingRegion; region != null; region = region.EnclosingRegion)
            {
                if (region.Kind == ControlFlowRegionKind.Try && region.EnclosingRegion?.Kind == ControlFlowRegionKind.TryAndFinally)
                {
                    _erased.Add(region.EnclosingRegion);
                    break;
                }
            }
        }

        /// <summary>The async stream an await foreach enumerates, evaluated: a library's (its receiver not null, CSV1013), through ConfigureAwait and WithCancellation.</summary>
        private void AsyncStream(IInvocationOperation getEnumerator)
        {
            var op = Unconverted(getEnumerator.Instance ?? getEnumerator.Arguments.FirstOrDefault()?.Value);
            while (op is IInvocationOperation c && c.TargetMethod.Name is "ConfigureAwait" or "WithCancellation")
            {
                foreach (var a in c.Arguments.Where(a => a.Parameter.Ordinal > 0 || c.Instance != null))
                {
                    if (InSubset(a.Value.Type))
                    {
                        Expr(a.Value);
                    }
                }
                op = Unconverted(c.Instance ?? c.Arguments.First(a => a.Parameter.Ordinal == 0).Value);
            }
            if (op is IInvocationOperation src && src.TargetMethod.DeclaringSyntaxReferences.Length == 0 && !SpecSymbols.IsSpecClass(src.TargetMethod.ContainingType))
            {
                if (src.Instance != null)
                {
                    var recv = Expr(Unconverted(src.Instance));
                    if (!src.Instance.Type.IsValueType)
                    {
                        Emit(KCheck.Of(NotNull(recv), "CSV1013", src.Instance.Syntax, $"'{src.Instance.Syntax}' might be null in '{src.Syntax}'"));
                    }
                }
                foreach (var a in src.Arguments.OrderBy(a => a.Parameter.Ordinal))
                {
                    if (a.Parameter.RefKind != RefKind.None || !InSubset(a.Value.Type))
                    {
                        throw new NotTranslated("an argument of " + src.TargetMethod.Name);
                    }
                    else
                    {
                        Expr(a.Value);
                    }
                }
                return;
            }
            throw new NotTranslated("an await foreach over " + op?.Syntax);
        }

        private KExpr Current(ForEach fe)
        {
            if (fe.Mat != null)
            {
                return Sel(fe.Mat, new KVar(fe.Index));
            }
            // (an enumerator the kernel doesn't look into: a value of the element's type, not null where that says so)
            if (fe.Opaque)
            {
                var e = Declare("t$" + _temps++, fe.Element);
                Emit(KHavoc.Of(e));
                if (IsNullable(fe.Element) && NotNullable(fe.Element))
                {
                    Emit(KAssume.Of(NotNull(new KVar(e))));
                }
                return new KVar(e);
            }
            // (an array's element, read where the loop is: as a[i] is, CSV1027 alongside other code)
            if (fe.Version == null && fe.Collection == null && !fe.String)
            {
                HeldCell(new KVar(fe.Array), fe.At, write: false);
            }
            if (fe.Version == null)
            {
                return CurrentOf(fe);
            }
            // (through the enumerator: what it gives isn't known; a dictionary's, a pair it has)
            if (!_p.Warnings.Any(w => w.Message.Contains("'Current'") && w.Span.Equals(fe.At.GetLocation().GetLineSpan())))
            {
                _p.Warnings.Add(new VerificationDiagnostic("CSV1900", false, "property 'Current' of Enumerator is not modeled; its value is unknown", fe.At.GetLocation().GetLineSpan()));
            }
            var v = Declare("t$" + _temps++, fe.Element);
            Emit(KHavoc.Of(v));
            if (fe.View == "Keys")
            {
                // (a key it has: never null)
                Emit(KAssume.Of(Sel(ModelOf("Domain", fe.Collection).Name, new KVar(fe.Array), Keyed(new KVar(v), fe.Element))));
                if (fe.Element.IsReferenceType)
                {
                    Emit(KAssume.Of(NotNull(new KVar(v))));
                }
            }
            else if (fe.View == "Values") { } // (a value it has: not modeled)
            else if (CollectionKind(fe.Collection) == "Dictionary")
            {
                var key = Pair(new KVar(v), fe.Element, "Key");
                var value = Pair(new KVar(v), fe.Element, "Value");
                Emit(KAssume.Of(
                AndAlso(Sel(ModelOf("Domain", fe.Collection).Name, new KVar(fe.Array), key),
                             Eq(Sel(ModelOf("Entries", fe.Collection).Name, new KVar(fe.Array), key), value))));
            }
            // (a set's: one of its members, as the version at the start has them, in some order)
            else if (CollectionKind(fe.Collection) == "HashSet")
            {
                Emit(KAssume.Of(Sel(ModelOf("Members", fe.Collection).Name, new KVar(fe.Array), Keyed(new KVar(v), fe.Element))));
            }
            return new KVar(v);
        }

        /// <summary>A dictionary's pair's Key or Value.</summary>
        private KExpr Pair(KExpr pair, ITypeSymbol type, string member)
        {
            var args = ((INamedTypeSymbol)type).TypeArguments;
            var (k, v) = (Kind(args[0]), Kind(args[1]));
            _p.Pairs.Add((k, v));
            return new KOp(member == "Key" ? "$kvp.Key." + k : "$kvp.Value." + v, pair);
        }

        private static KExpr CurrentOf(ForEach fe) => fe.Collection != null ? Sel(ModelOf("Items", fe.Collection).Name, new KVar(fe.Array), new KVar(fe.Index)) :
            new KElem
            {
                String = fe.String,
                Array = new KVar(fe.Array),
                Index = new KVar(fe.Index),
                ArrayType = fe.String ? null : fe.Type,
                At = fe.At,
                ArrayAt = fe.At,
            };

        /// <summary>A loop body that calls nothing that may change a list: only specifications, [Pure] members and lists' [Pure] stubs.</summary>
        private bool ChangesNoList(SyntaxNode body) => body.DescendantNodesAndSelf().Select(n => _model.GetOperation(n)).Where(o => o != null && !InSpec(o.Syntax)).All(o => o switch
        {
            IInvocationOperation inv => SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType) || _contractOf?.Invoke(inv.TargetMethod) is Contract c && (c.IsPure || c.IsLemma),
            IObjectCreationOperation oc => !IsCollection(oc.Type) && (oc.Constructor == null || oc.Constructor.DeclaringSyntaxReferences.Length > 0 && _contractOf?.Invoke(oc.Constructor) is Contract cc && cc.IsPure),
            IPropertyReferenceOperation pr => !IsCollection(pr.Instance?.Type) || !(pr.Parent is IAssignmentOperation a && a.Target == pr),
            IAnonymousFunctionOperation _ => false,
            _ => true,
        });

        /// <summary>The collection's length: an array's or a string's, or a list's Size.</summary>
        private KExpr LengthOf(ForEach fe, bool inSpec = false) => fe.Count != null ? new KVar(fe.Count) : fe.Collection != null
            ? Model("Size", fe.Collection, new KVar(fe.Array))
            : new KLen
            {
                String = fe.String,
                Array = new KVar(fe.Array),
                InSpec = inSpec,
                At = fe.At,
                ArrayAt = fe.At,
            };

        /// <summary>A foreach's index stays within its collection: the loop's first invariant (it holds by itself).</summary>
        private void ForEachInvariants()
        {
            foreach (var fe in _forEachAt.Values)
            {
                if (!_p.Invariants.TryGetValue(fe.Head, out var list))
                {
                    _p.Invariants[fe.Head] = list = new List<KSpec>();
                }
                var i = new KVar(fe.Index);
                // (through an enumerator: at most as many as the collection had where the loop began)
                list.Insert(0, KSpec.Of(
                    fe.Opaque ? Le(KLit.Zero, i)
                  : fe.Version == null ? AndAlso(Le(KLit.Zero, i), Le(i, LengthOf(fe, true)))
                  : fe.Size0 != null ? AndAlso(Le(KLit.Zero, i), Le(i, new KVar(fe.Size0)))
                  : Le(KLit.Zero, i),
                    fe.At));
            }
        }
    }
}
