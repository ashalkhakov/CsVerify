#nullable enable
namespace CsVerify.Ef
{
    /// <summary>
    /// A library context's model, written out: the class it marks is the context's OnModelCreating as the library
    /// writes it, in EF's fluent API, which the verifier reads as it reads the program's (keys, unique indexes,
    /// concurrency tokens), with the program's context's type arguments for its own type parameters. Trusted, as
    /// stubs are: EfConformanceTests compare each with the model EF builds.
    /// </summary>
    [System.AttributeUsage(System.AttributeTargets.Class)]
    public sealed class ModelOfAttribute : System.Attribute
    {
        /// <summary>The library's context (a generic one unbound: typeof(IdentityUserContext&lt;,,,,&gt;)).</summary>
        public ModelOfAttribute(System.Type context) { }
    }
}
