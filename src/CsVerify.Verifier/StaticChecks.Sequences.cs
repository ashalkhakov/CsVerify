using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// A sequence writes nothing as it is enumerated (CSV1037). A method reads an IEnumerable&lt;T&gt; it is handed as
    /// a value of the state: enumerating it changes nothing. So what makes a sequence that would write as it is
    /// enumerated must enumerate it where it makes it, where what it writes is seen: a query a library member makes
    /// of a lambda or a method that writes (xs.Select(x => { n = x; return x; })), an iterator whose body writes, and
    /// an object of a class of the program's whose enumerator writes. Handed on (an argument, a result, a field), it
    /// is reported.
    /// </summary>
    internal partial class StaticChecks
    {
        internal const string QuietSequenceId = "CSV1037";

        private void CheckSequences(IOperation body)
        {
            if (body == null)
            {
                return;
            }
            foreach (var op in Own(body))
            {
                switch (op)
                {
                    // (a library member that keeps the delegates it is handed for when its sequence is enumerated)
                    case IInvocationOperation call when IsLibrary(call.TargetMethod) && IsHandedSequence(call.Type):
                        foreach (var handed in call.Arguments.Where(a => a.Parameter?.Type.TypeKind == TypeKind.Delegate))
                        {
                            if (Writes(handed.Value) is string what && !EnumeratedHere(call, views: true))
                            {
                                Report(QuietSequenceId, handed.Value.Syntax,
                                       $"'{call.TargetMethod.Name}' runs this as its sequence is enumerated, and it {what}; but the sequence is handed on, and enumerating a sequence that was handed on is taken to write nothing. Enumerate it here (ToList, ToArray)", isError: true);
                            }
                        }
                        break;
                    // (an iterator's body runs as its sequence is enumerated)
                    case IInvocationOperation call when IteratorWrites(call.TargetMethod) is string what && !EnumeratedHere(call, views: false):
                        Report(QuietSequenceId, call.Syntax,
                               $"'{call.TargetMethod.Name}' is an iterator, which {what} as its sequence is enumerated; but the sequence is kept or handed on, and enumerating one then is taken to write nothing. Enumerate it where it is made (a foreach over the call, or ToList on it)", isError: true);
                        break;
                    case IPropertyReferenceOperation read when read.Property.GetMethod != null && IteratorWrites(read.Property.GetMethod) is string what && !EnumeratedHere(read, views: false):
                        Report(QuietSequenceId, read.Syntax,
                               $"'{read.Property.Name}' is an iterator, which {what} as its sequence is enumerated; but the sequence is kept or handed on, and enumerating one then is taken to write nothing. Enumerate it where it is made (a foreach over it, or ToList on it)", isError: true);
                        break;
                    // (an object of the program's, handed on as a sequence: its enumerator runs then)
                    case IConversionOperation conversion when IsHandedSequence(conversion.Type) && conversion.Operand.Type is INamedTypeSymbol from && !IsHandedSequence(from) &&
                                                              EnumeratorWrites(from) is string what && !EnumeratedHere(conversion, views: false):
                        Report(QuietSequenceId, conversion.Operand.Syntax,
                               $"enumerating a {from.Name} {what}; but it is handed on as a sequence, and enumerating one then is taken to write nothing. Enumerate it here (ToList, ToArray)", isError: true);
                        break;
                }
            }
        }

        /// <summary>The operations of a body, but those of a lambda or a local function inside it (checked as its own).</summary>
        private static IEnumerable<IOperation> Own(IOperation body)
        {
            var work = new Stack<IOperation>();
            work.Push(body);
            while (work.Count > 0)
            {
                var op = work.Pop();
                yield return op;
                foreach (var child in op.ChildOperations)
                {
                    if (!(child is IAnonymousFunctionOperation || child is ILocalFunctionOperation))
                    {
                        work.Push(child);
                    }
                }
            }
        }

        private static bool IsLibrary(IMethodSymbol m) =>
            m.OriginalDefinition.DeclaringSyntaxReferences.Length == 0 && m.MethodKind != MethodKind.DelegateInvoke && !SpecSymbols.IsSpecClass(m.ContainingType);

        /// <summary>A sequence that may be read later than it is made: IEnumerable, IEnumerable&lt;T&gt; and what LINQ's queries are typed as.</summary>
        private static bool IsHandedSequence(ITypeSymbol t) =>
            t is INamedTypeSymbol { TypeKind: TypeKind.Interface } n &&
            n.OriginalDefinition.ToDisplayString() is "System.Collections.IEnumerable" or "System.Collections.Generic.IEnumerable<T>" or "System.Linq.IOrderedEnumerable<TElement>" or
                "System.Collections.Generic.IReadOnlyCollection<T>" or "System.Collections.Generic.IReadOnlyList<T>" or "System.Collections.Generic.ICollection<T>" or "System.Collections.Generic.IList<T>";

        // ------------------------------------------------------------------ what writes

        /// <summary>What a delegate handed to a library member may write when it runs (null: nothing).</summary>
        private string Writes(IOperation value)
        {
            while (value is IConversionOperation c && c.IsImplicit)
            {
                value = c.Operand;
            }
            switch (value)
            {
                case IDelegateCreationOperation { Target: IAnonymousFunctionOperation lambda }: return LambdaWrites(lambda);
                case IAnonymousFunctionOperation lambda: return LambdaWrites(lambda);
                case IDelegateCreationOperation { Target: IMethodReferenceOperation reference }: return Calls(reference.Method, null);
                case IParameterReferenceOperation p when SaidToChangeNothing(p.Parameter): return null;
                default: return $"isn't known to change nothing (a parameter's is, with Spec.Requires(Spec.ChangesNothing(...)))";
            }
        }

        /// <summary>A delegate parameter whose method requires Spec.ChangesNothing of it.</summary>
        private bool SaidToChangeNothing(IParameterSymbol p) =>
            p.ContainingSymbol is IMethodSymbol m && _engine.ContractOf(m) is Contract c &&
            c.OwnRequires.SelectMany(r => r.DescendantsAndSelf()).OfType<IInvocationOperation>().Any(i =>
                SpecSymbols.IsSpecClass(i.TargetMethod.ContainingType) && i.TargetMethod.Name == "ChangesNothing" &&
                i.Arguments.Any(a => a.Value.DescendantsAndSelf().OfType<IParameterReferenceOperation>().Any(x => SymbolEqualityComparer.Default.Equals(x.Parameter, p))));

        private string LambdaWrites(IAnonymousFunctionOperation lambda)
        {
            foreach (var op in lambda.Body.DescendantsAndSelf())
            {
                if (SpecSymbols.EnclosingSpecCall(op.Syntax, _model) != null)
                {
                    continue;
                }
                switch (op)
                {
                    case IAssignmentOperation a when Written(a.Target, lambda) is string what: return what;
                    case IIncrementOrDecrementOperation i when Written(i.Target, lambda) is string what: return what;
                    case IDeconstructionAssignmentOperation d when d.Target.DescendantsAndSelf().Select(t => Written(t, lambda)).FirstOrDefault(w => w != null) is string what: return what;
                    case IArgumentOperation arg when arg.Parameter != null && arg.Parameter.RefKind is RefKind.Ref or RefKind.Out && Written(arg.Value, lambda) is string what: return what;
                    case IInvocationOperation call when Calls(call.TargetMethod, call) is string what: return what;
                    case IObjectCreationOperation made when made.Constructor != null && ConstructorWrites(made.Constructor) is string what: return what;
                    case IPropertyReferenceOperation read when read.Property.GetMethod is IMethodSymbol getter && getter.DeclaringSyntaxReferences.Length > 0 &&
                                                               !(read.Parent is IAssignmentOperation set && set.Target == read) && Calls(getter, null) is string what: return what;
                    case IBinaryOperation b when b.OperatorMethod != null && Calls(b.OperatorMethod, null) is string what: return what;
                    case IUnaryOperation u when u.OperatorMethod != null && Calls(u.OperatorMethod, null) is string what: return what;
                    case IConversionOperation c when c.OperatorMethod != null && Calls(c.OperatorMethod, null) is string what: return what;
                }
            }
            return null;
        }

        /// <summary>What a write through this target changes that outlives the lambda's call (null: nothing: its own variable, a new object's member).</summary>
        private static string Written(IOperation target, IAnonymousFunctionOperation lambda)
        {
            switch (target)
            {
                case ILocalReferenceOperation l:
                    return lambda.Syntax.Span.Contains(l.Local.Locations.FirstOrDefault()?.SourceSpan ?? default) ? null : $"writes '{l.Local.Name}', a variable it captures";
                case IParameterReferenceOperation p:
                    return lambda.Syntax.Span.Contains(p.Parameter.Locations.FirstOrDefault()?.SourceSpan ?? default) ? null : $"writes '{p.Parameter.Name}', a variable it captures";
                // (an initializer's, or of an object the lambda made and holds in a variable of its own: the new object's)
                case IMemberReferenceOperation { Instance: IInstanceReferenceOperation { ReferenceKind: InstanceReferenceKind.ImplicitReceiver } }: return null;
                case IMemberReferenceOperation { Instance: ILocalReferenceOperation made } when lambda.Syntax.Span.Contains(made.Local.Locations.FirstOrDefault()?.SourceSpan ?? default) &&
                                                                                           made.Local.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is Microsoft.CodeAnalysis.CSharp.Syntax.VariableDeclaratorSyntax
                                                                                           {
                                                                                               Initializer.Value: Microsoft.CodeAnalysis.CSharp.Syntax.BaseObjectCreationExpressionSyntax _
                                                                                           }:
                    return null;
                case IMemberReferenceOperation m: return $"writes '{m.Member.Name}'";
                case IArrayElementReferenceOperation _: return "writes an array's element";
                case ITupleOperation t: return t.Elements.Select(e => Written(e, lambda)).FirstOrDefault(w => w != null);
                case IDeclarationExpressionOperation _: case IDiscardOperation _: return null;
                default: return null;
            }
        }

        /// <summary>What a call of this method may write, as "calls 'M', which ..." (null: nothing).</summary>
        private string Calls(IMethodSymbol m, IInvocationOperation call)
        {
            if (SpecSymbols.IsSpecClass(m.ContainingType) || SpecSymbols.IsModel(m.ReducedFrom ?? m.OriginalDefinition))
            {
                return null;
            }
            if (m.MethodKind == MethodKind.DelegateInvoke)
            {
                return call?.Instance is IParameterReferenceOperation p && SaidToChangeNothing(p.Parameter) ? null
                    : $"calls '{call?.Instance?.Syntax.ToString() ?? m.Name}', a delegate that isn't known to change nothing";
            }
            if (m.OriginalDefinition.DeclaringSyntaxReferences.Length > 0)
            {
                return MethodWrites(m) is string what ? $"calls '{m.Name}', which {what}" : null;
            }
            if (_engine.ContractOf(m) is Contract c && c.IsPure)
            {
                return null;
            }
            // (a query's operator, in a lambda: a sequence it reads writes nothing, as any that is handed on; the
            // delegates it is handed that aren't lambdas, seen here, and its elements' own code may)
            if (call != null && m.ContainingType?.ToDisplayString() == "System.Linq.Enumerable")
            {
                return call.Arguments.Where(a => a.Parameter?.Type.TypeKind == TypeKind.Delegate && !(a.Value.Syntax is Microsoft.CodeAnalysis.CSharp.Syntax.AnonymousFunctionExpressionSyntax))
                           .Select(a => Writes(a.Value)).FirstOrDefault(w => w != null) is string by ? $"calls '{m.Name}' with a delegate that {by}"
                    : _engine.Fields.ElementsRun(m) ? $"calls '{m.Name}', which may run its elements' code" : null;
            }
            // (a library's: what its stub says it changes, or by what this call hands it)
            var (models, _) = _engine.Fields.WritesOf(m);
            bool runs = call != null ? _engine.Fields.WritesFieldsAt(call) : _engine.Fields.RunsUserCode(m);
            return models.Count > 0 || runs || _engine.MayWriteHeap(m) ? $"calls '{m.Name}', which may change what it is handed" : null;
        }

        /// <summary>What a method of the program's may write, by the effects analysis (null: nothing).</summary>
        private string MethodWrites(IMethodSymbol m)
        {
            var (fields, all) = _engine.Fields.WritesOf(m);
            return all ? "may write anything"
                : fields.Count > 0 ? $"writes '{fields.Select(f => f.Name).OrderBy(n => n, System.StringComparer.Ordinal).First()}'"
                : _engine.MayWriteHeap(m) ? "may write an array's element" : null;
        }

        /// <summary>What a constructor writes other than the new object's own (a library collection's models are the new object's).</summary>
        private string ConstructorWrites(IMethodSymbol ctor)
        {
            var (fields, all) = _engine.Fields.WritesOf(ctor);
            bool library = ctor.OriginalDefinition.DeclaringSyntaxReferences.Length == 0;
            return all ? $"makes a {ctor.ContainingType.Name}, whose constructor may write anything"
                : !library && fields.Count > 0 ? $"makes a {ctor.ContainingType.Name}, whose constructor writes '{fields.First().Name}'" : null;
        }

        /// <summary>What a source iterator's body writes as its sequence is enumerated, or that of a member that may override this one (null: nothing, or no iterator).</summary>
        private string IteratorWrites(IMethodSymbol m)
        {
            m = (m.ReducedFrom ?? m).OriginalDefinition;
            if (!IsHandedSequence(m.ReturnType))
            {
                return null;
            }
            foreach (var body in new[] { m }.Concat(Engine.IsOverridable(m) ? _engine.Fields.Overrides(m) : Enumerable.Empty<IMethodSymbol>()))
            {
                if (body.IsIterator && body.DeclaringSyntaxReferences.Length > 0 && MethodWrites(body) is string what)
                {
                    return what;
                }
            }
            return null;
        }

        /// <summary>
        /// What enumerating an object of this type of the program's may write: its GetEnumerator (of any class of the
        /// program's the object may be), and the program's own enumerators, but for an enumerator's own fields.
        /// </summary>
        private string EnumeratorWrites(INamedTypeSymbol from)
        {
            if (from.OriginalDefinition.DeclaringSyntaxReferences.Length == 0)
            {
                return null;
            }
            var sources = _engine.SourceTypes.Where(s => DataTypes.Derives(s, from.OriginalDefinition) || s.AllInterfaces.Any(i => SymbolEqualityComparer.Default.Equals(i.OriginalDefinition, from.OriginalDefinition))).ToList();
            bool handWritten = false;
            foreach (var s in sources)
            {
                foreach (var get in s.AllInterfaces.Where(i => i.Name == "IEnumerable").SelectMany(i => i.GetMembers("GetEnumerator")).Select(s.FindImplementationForInterfaceMember).OfType<IMethodSymbol>())
                {
                    if (get.DeclaringSyntaxReferences.Length == 0)
                    {
                        continue;
                    }
                    if (MethodWrites(get) is string what)
                    {
                        return what;
                    }
                    handWritten |= !get.IsIterator;
                }
            }
            if (!handWritten)
            {
                return null;
            }
            // (an enumerator of the program's: MoveNext and the rest may write its own fields, which nothing else reads,
            // unless it is the sequence too)
            foreach (var e in _engine.SourceTypes.Where(s => s.AllInterfaces.Any(i => i.ToDisplayString() == "System.Collections.IEnumerator")))
            {
                bool itself = e.AllInterfaces.Any(i => i.Name == "IEnumerable");
                foreach (var member in e.AllInterfaces.Where(i => i.Name is "IEnumerator" or "IDisposable").SelectMany(i => i.GetMembers()).Select(e.FindImplementationForInterfaceMember).OfType<IMethodSymbol>())
                {
                    if (member.DeclaringSyntaxReferences.Length == 0)
                    {
                        continue;
                    }
                    var (fields, all) = _engine.Fields.WritesOf(member);
                    var other = fields.FirstOrDefault(f => itself || !SymbolEqualityComparer.Default.Equals(f.ContainingType, e));
                    if (all || other != null || _engine.MayWriteHeap(member))
                    {
                        return all ? $"runs '{e.Name}.{member.Name}', which may write anything" : other != null ? $"runs '{e.Name}.{member.Name}', which writes '{other.Name}'" : $"runs '{e.Name}.{member.Name}', which may write an array's element";
                    }
                }
            }
            return null;
        }

        // ------------------------------------------------------------------ where it is enumerated

        /// <summary>
        /// Is this sequence enumerated where it is made: by a foreach over it, or by a library member that reads it
        /// through (LINQ's that give no sequence, a collection's constructor or AddRange, string.Join), itself or
        /// queries made of it? With views, also through a local that is only ever so read (LINQ reads a local's query
        /// where the local is used).
        /// </summary>
        private bool EnumeratedHere(IOperation sequence, bool views)
        {
            var current = sequence;
            while (true)
            {
                var parent = current.Parent;
                while (parent is IConversionOperation || parent is IParenthesizedOperation)
                {
                    current = parent;
                    parent = current.Parent;
                }
                switch (parent)
                {
                    case IArgumentOperation { Parent: IInvocationOperation call } when IsLibrary(call.TargetMethod):
                        if (IsHandedSequence(call.Type))
                        {
                            current = call;
                            continue;
                        }
                        return ReadsThrough(call.TargetMethod);
                    case IArgumentOperation { Parent: IObjectCreationOperation made }:
                        return made.Constructor != null && ReadsThrough(made.Constructor);
                    case IInvocationOperation call when call.Instance == current && IsLibrary(call.TargetMethod):
                        return ReadsThrough(call.TargetMethod);
                    case IForEachLoopOperation loop:
                        return loop.Collection == current;
                    case IVariableInitializerOperation { Parent: IVariableDeclaratorOperation declared } when views:
                        return OnlyEnumerated(declared.Symbol);
                    case ISimpleAssignmentOperation { Target: ILocalReferenceOperation local, Parent: IExpressionStatementOperation _ } assigned when views && assigned.Value == current:
                        return OnlyEnumerated(local.Local);
                    default:
                        return false;
                }
            }
        }

        /// <summary>A library member that enumerates the sequence it is handed before it returns, and keeps none of it.</summary>
        private static bool ReadsThrough(IMethodSymbol m)
        {
            var type = m.ContainingType?.OriginalDefinition;
            string ns = type?.ContainingNamespace?.ToDisplayString();
            return type?.ToDisplayString() == "System.Linq.Enumerable" && !IsHandedSequence(m.ReturnType) && m.Name != "ToLookup" ||
                   ns == "System.Collections.Generic" && type.TypeKind == TypeKind.Class ||
                   type?.SpecialType == SpecialType.System_String && m.Name is "Join" or "Concat";
        }

        /// <summary>A local every use of which, in this body, enumerates it where it is used; none in a lambda or a local function.</summary>
        private bool OnlyEnumerated(ILocalSymbol local)
        {
            var root = _model.GetOperation(_contract.Declaration);
            if (root == null)
            {
                return false;
            }
            foreach (var use in root.DescendantsAndSelf().OfType<ILocalReferenceOperation>().Where(u => SymbolEqualityComparer.Default.Equals(u.Local, local)))
            {
                // (its own writes aren't reads)
                if (use.Parent is ISimpleAssignmentOperation set && set.Target == use)
                {
                    continue;
                }
                bool nested = false;
                for (var p = use.Parent; p != null && p != root; p = p.Parent)
                {
                    nested |= p is IAnonymousFunctionOperation || p is ILocalFunctionOperation;
                }
                if (nested || !EnumeratedHere(use, views: false))
                {
                    return false;
                }
            }
            return true;
        }
    }
}
