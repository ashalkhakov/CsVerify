using System.Linq;
using CsVerify.Verifier;
using Microsoft.CodeAnalysis;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// A referenced project (--project-reference) is compiled as a project of its own, which the program's compilation
    /// references in place of its assembly: its types and contracts are the program's, its code is called by its
    /// contracts and not verified.
    /// </summary>
    public class ReferencedProjectTests
    {
        [Fact]
        public void ARecordStructOfAReferencedProject_IsOfTheSubset()
        {
            // (#111: a strongly typed id of a domain project)
            const string library = "namespace Model { public readonly record struct ParcelId(System.Guid Value); }";
            const string source = @"using Model;
public static class Parcels
{
    public static int Plain(ParcelId id, int x) => x + 0;
    public static Guid ValueOf(ParcelId id) => id.Value;
    public static ParcelId Make(Guid g) { Spec.Ensures<ParcelId>(r => r.Value == g); return new ParcelId(g); }
    public static void Same(Guid g) { var a = Make(g); var b = new ParcelId(g); Spec.Assert(a == b); }
}";
            var r = Harness.VerifyWithLibrary(library, source, sources: true);
            foreach (var m in new[] { "Plain", "ValueOf", "Make", "Same" })
            {
                Assert.True(r.Errors(m).Length == 0, r.Explain(m));
            }
            // (from its assembly alone, it is a library's struct)
            Assert.Equal(new[] { "CSV1902" }, Harness.VerifyWithLibrary(library, source).Errors("Plain"));
        }

        [Fact]
        public void AContractClassOfAReferencedProject_IsRead()
        {
            // (#114: the interface's project holds its contract class)
            var r = Harness.VerifyWithLibrary(@"using CsVerify;
namespace Lib
{
    public interface IStore { int Take(int amount); }
    [ContractClassFor(typeof(IStore))]
    internal abstract class StoreContract : IStore
    {
        public int Take(int amount) { Spec.Requires(amount > 0); return 0; }
    }
}", @"using Lib;
public sealed class Store : IStore
{
    public int Take(int amount) { Spec.Assert(amount > 0); return amount; }
}
public static class Takes
{
    public static int One(IStore s) => s.Take(1);
    public static int None(IStore s) => s.Take(0);
}", sources: true);
            Assert.True(r.Errors("Store.Take").Length == 0, r.Explain("Store.Take"));
            Assert.True(r.Errors("One").Length == 0, r.Explain("One"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("None"));
        }

        [Fact]
        public void AReferencedProjectsCode_IsCalledByItsContract_NotVerified()
        {
            var r = Harness.VerifyWithLibrary(@"using CsVerify;
namespace Lib
{
    public static class Numbers
    {
        // (wrong, and its project's to find: here only its contract is used)
        public static int Positive(int x) { Spec.Ensures<int>(r => r > 0); return x; }
        public static int First(int[] a) => a[0];
    }
}", @"using Lib;
public static class Uses
{
    public static void Calls(int x) { var p = Numbers.Positive(x); Spec.Assert(p > 0); }
}", sources: true);
            Assert.Equal(new[] { "Uses.Calls" }, r.Methods.Select(m => m.Name).ToArray());
            Assert.True(r.Errors("Calls").Length == 0, r.Explain("Calls"));
        }

        [Fact]
        public void AReferencedProjectsGlobalUsings_AreItsOwn()
        {
            // (a global using is the whole compilation's: the library's System.Timers would make the program's Timer,
            // System.Threading's, ambiguous)
            var r = Harness.VerifyWithLibrary(@"global using System.Timers;
namespace Lib { public static class Clocks { public static double Of(Timer t) => 1.0; public static int One() => 1; } }", @"using System.Threading;
public static class Uses
{
    public static bool Has(Timer? t) => t != null;
    public static int One() => Lib.Clocks.One();
}", sources: true);
            Assert.True(r.Errors("Uses.One").Length == 0, r.Explain("Uses.One"));
        }

        [Fact]
        public void AReferencedProjectsAlias_IsItsOwn()
        {
            // (its global alias Text is its project's; the program's Text is a class of its own)
            var r = Harness.VerifyWithLibrary(@"global using Text = System.String;
namespace Lib { public static class Names { public static Text Of(Text t) => t; } }", @"public sealed class Text { public int N; }
public static class Uses
{
    public static int N(Text t) => t.N;
    public static string Name(string s) => Lib.Names.Of(s);
}", sources: true);
            Assert.True(r.Errors("Uses.N").Length == 0, r.Explain("Uses.N"));
            Assert.True(r.Errors("Name").Length == 0, r.Explain("Name"));
        }

        [Fact]
        public void AReferencedProjectsErrors_AreReported()
        {
            var project = new CsVerify.Verifier.ProjectReference { AssemblyName = "Broken" };
            var dir = System.IO.Path.Combine(System.IO.Path.GetTempPath(), "CsVerifyBroken" + System.Guid.NewGuid().ToString("N"));
            System.IO.Directory.CreateDirectory(dir);
            var file = System.IO.Path.Combine(dir, "Broken.cs");
            System.IO.File.WriteAllText(file, "public static class Broken { public static int F() => Missing.G(); }");
            project.Sources.Add(file);
            var options = new CsVerify.Verifier.VerifierOptions();
            options.ProjectReferences.Add(project);
            var r = CsVerify.Verifier.Engine.VerifySources(new[] { ("Test.cs", "public static class P { public static int F() => 1; }") }, options);
            Assert.Contains(r.CompilationErrors, d => d.Id == "CS0103");
            System.IO.Directory.Delete(dir, true);
        }

        [Fact]
        public void AnAssemblyTwoProjectsReference_IsTheProgramsVersion()
        {
            // (#117: a project's older version of a package beside the program's; the build resolves the program's)
            var dir = System.IO.Path.Combine(System.IO.Path.GetTempPath(), "CsVerifyVersions" + System.Guid.NewGuid().ToString("N"));
            try
            {
                string Package(string version)
                {
                    var folder = System.IO.Path.Combine(dir, version);
                    System.IO.Directory.CreateDirectory(folder);
                    var path = System.IO.Path.Combine(folder, "Pkg.dll");
                    var c = Microsoft.CodeAnalysis.CSharp.CSharpCompilation.Create("Pkg",
                        new[] { Microsoft.CodeAnalysis.CSharp.CSharpSyntaxTree.ParseText($"[assembly: System.Reflection.AssemblyVersion(\"{version}\")] namespace Pkg {{ public sealed class Money {{ public long Cents {{ get; set; }} }} public static class Moneys {{ public static long Of(this Money m) => m.Cents; }} }}") },
                        Engine.FrameworkReferences(), new Microsoft.CodeAnalysis.CSharp.CSharpCompilationOptions(Microsoft.CodeAnalysis.OutputKind.DynamicallyLinkedLibrary));
                    Assert.True(c.Emit(path).Success);
                    return path;
                }
                var older = Package("1.0.0.0");
                var newer = Package("2.0.0.0");
                var lib = System.IO.Path.Combine(dir, "Lib.cs");
                System.IO.File.WriteAllText(lib, "namespace Lib { public sealed class Marker { public Pkg.Money Price { get; set; } = new Pkg.Money(); } }");
                var options = new VerifierOptions { AssemblyName = "App" };
                options.References.Add(newer);
                var project = new ProjectReference { AssemblyName = "Lib", Nullable = Microsoft.CodeAnalysis.NullableContextOptions.Enable };
                project.Sources.Add(lib);
                project.References.Add(older);
                options.ProjectReferences.Add(project);
                var r = Engine.VerifySources(new[] { ("Test.cs", @"using CsVerify; using Pkg;
public static class Prices
{
    public static long Of(Lib.Marker m) { Spec.Requires(m.Price != null); return m.Price.Of(); }
    public static Money Make() => new Money();
}") }, options);
                Assert.True(r.CompilationErrors.Count == 0, string.Join("\n", r.CompilationErrors));
                Assert.Empty(r.Warnings);
            }
            finally { try { System.IO.Directory.Delete(dir, true); } catch (System.IO.IOException) { } }
        }
    }
}
