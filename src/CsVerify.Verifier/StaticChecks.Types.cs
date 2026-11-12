using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Dynamic types of ordinary objects: <c>isa(o, T)</c>, "o is an instance of T". A non-null value of a static
    /// type is an instance of it and of its supertypes; an object made by <c>new C()</c> is exactly a C. Classes form
    /// a tree (single inheritance), so unrelated classes have no instance in common, and a sealed class's instances
    /// are of no type but its supertypes. <c>is</c>, <c>as</c> and casts read isa. Generic types are left out (their
    /// instantiations would share one name), as are data records (they have tags) and value types.
    /// </summary>
    internal sealed partial class StaticChecks
    {
    }
}
