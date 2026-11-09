#nullable enable
namespace CsVerify.Ef
{
    using Microsoft.EntityFrameworkCore;

    /// <summary>
    /// What a DbContext keeps between calls, as ghost state the verifier reads and updates at each Entity Framework
    /// call (MethodVerifier.EntityFramework): which entities it tracks and how, whether it has changes not yet saved,
    /// an open transaction, or a failed save behind it. Compiled in only for programs that reference EF Core.
    /// </summary>
    public static class Tracker
    {
        // (EntityState's values)
        /// <summary>Not tracked by the context.</summary>
        public const int Detached = 0;
        public const int Unchanged = 1;
        public const int Deleted = 2;
        public const int Modified = 3;
        public const int Added = 4;

        /// <summary>How the context tracks the entity: an EntityState, <see cref="Detached"/> to <see cref="Added"/>.</summary>
        [Model]
        public static int State(this DbContext context, object entity)
        {
            Spec.Ensures<int>(r => Detached <= r && r <= Added);
            throw null!;
        }

        /// <summary>
        /// Changes the context holds that SaveChanges would write: an entity added, removed or marked modified, or a
        /// tracked entity's field written since it was read or saved.
        /// </summary>
        [Model] public static bool Unsaved(this DbContext context) => throw null!;

        /// <summary>A transaction is open on the context's connection (Database.CurrentTransaction is not null).</summary>
        [Model] public static bool InTransaction(this DbContext context) => throw null!;

        /// <summary>
        /// SaveChanges failed on it (DbUpdateException, DbUpdateConcurrencyException): what it tracks no longer says what
        /// the database holds, so the context is done with.
        /// </summary>
        [Model] public static bool Failed(this DbContext context) => throw null!;

        /// <summary>
        /// The tracked entity's values may not be the database's: ExecuteUpdate or ExecuteDelete on its table ran after
        /// it was read, and changed rows without the tracker.
        /// </summary>
        [Model] public static bool Stale(this DbContext context, object entity) => throw null!;

        /// <summary>The context read the entity, without tracking it, in the method being verified.</summary>
        [Model] public static bool Read(this DbContext context, object entity) => throw null!;

        /// <summary>The entity's (first) concurrency token as the context read it (where <see cref="Read"/>).</summary>
        [Model] public static object? TokenRead(this DbContext context, object entity) => throw null!;

        /// <summary>
        /// The entity was read without tracking in the method being verified, which lets none of the entities it reads
        /// out (to a field, a call of the program, a lambda): no other code reaches it, so an await leaves it as it was.
        /// </summary>
        [Model] public static bool Unshared(object entity) => throw null!;

        /// <summary>The context saved changes outside a transaction in the method being verified.</summary>
        [Model] public static bool SavedAlone(this DbContext context) => throw null!;
    }
}
