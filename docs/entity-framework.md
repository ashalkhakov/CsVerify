# Entity Framework Core

For a program that references EF Core, the verifier reads queries on a `DbContext` as what the database runs, and
checks that the context is used as EF requires: its change tracker, transactions and concurrency tokens, and one
operation at a time. Nothing needs to be written for this: the model comes from the program's own EF configuration.
`samples/EntityFramework` has a program that verifies and one with a bug in each method.

## The model

Read from the sources, as EF reads them:
- **Entity types:** a context's `DbSet<T>` properties, the types its configuration names (`modelBuilder.Entity<T>()`,
  an `IEntityTypeConfiguration<T>`), and what their navigations lead to, in the program or in an assembly it references
  (a domain project's). A referenced entity's auto-properties (the compiler's backing field beside them, read from the
  assembly) are its fields, as a source class's are, and those with a setter, of any accessibility, its columns; its
  internal members are seen where `InternalsVisibleTo` grants them. A property with code of its own is neither. A derived type has its base classes' properties, and its root's key, query
  filters, unique indexes and concurrency tokens, as EF reads them from the root of the hierarchy. An entity of the
  program's may derive from a library's class (ASP.NET Core Identity's `IdentityUser<TKey>`): that class's
  auto-properties are its columns, read from the assembly, of the instantiation it derives from (`Id`, a `long` of
  `IdentityUser<long>`, the key by EF's convention), and a library context's `DbSet<T>` (`IdentityDbContext`'s
  `Users`) is a table as the program's are.
- **A library context's own configuration:** its `OnModelCreating` is the library's compiled code, which the verifier
  doesn't read. The Spec library has it written out for ASP.NET Core Identity (`CsVerify.Ef.Identity`, a `[ModelOf]`
  class for each of Identity's contexts that configures a model, read as the program's configuration is, with the
  program's context's type arguments): the users' and roles' keys, their unique `NormalizedUserName` and
  `NormalizedName`, their `ConcurrencyStamp` tokens, and the claims', logins', tokens' and user roles' keys. It is
  trusted, as stubs are, and `IdentityModelTests` compares it with the model EF builds. An entity a library context
  configures that no such model describes (a passkey's, which Identity maps by a schema version the program sets at
  run time; any of another library's context) is read no further: no key is taken by convention, and `Attach`,
  `Update` and a write of a column its library base declares aren't translated (CSV1902), as its concurrency tokens
  and row versions aren't known.
- **Owned and complex types** (`OwnsOne`, `OwnsMany`, `[Owned]`, `ComplexProperty`, `[ComplexType]`): columns of their
  owner, which EF always loads with it. They are neither entities nor navigations here, and nothing is said of them.
- **Keys:** `[Key]`, `HasKey(x => x.P)`, `HasKey(x => new { x.A, x.B })`, `HasKey("P")` or `HasKey(nameof(T.P))`, or EF's
  convention (`Id`, or the type's name and `Id`).
- **Unique values:** `[Index(..., IsUnique = true)]`, `HasIndex(...).IsUnique()`, `HasAlternateKey(...)`.
- **Concurrency tokens:** `[ConcurrencyCheck]`, `IsConcurrencyToken()`; row versions: `[Timestamp]`, `IsRowVersion()`.
- **Query filters:** `HasQueryFilter(x => ...)`.
- **Navigations:** properties of an entity type, or of a collection of one, and their foreign keys
  ([Tracking](#queries)).

A context in a referenced project (the context and its configuration in one project or two, the queries in another)
is read as one of the program's: the MSBuild target describes each referenced project that uses CsVerify too
(`--project-reference`), and the verifier compiles it as a project the program's compilation references
([Running](running.md)).

Fluent configuration is read in `OnModelCreating` and in `IEntityTypeConfiguration<T>.Configure`, whether `ApplyConfiguration`
or `ApplyConfigurationsFromAssembly` applies it. A `Configure` that a configuration class inherits from a generic base
(`KeyedConfiguration<T>`) is read for the class's entity, with the base's abstract members as the class overrides them,
where each override is an expression-bodied lambda (`protected override Expression<Func<Transfer, long>> Key => x =>
x.RowId;`); a key named by the member that lambda selects (`HasKey(((MemberExpression)Key.Body).Member.Name)`) is read
too, and so is one an interface's member names in a base over `T : IHasId` (`HasKey(c => c.Id)`): the entity's property
that implements it. `OnModelCreating` itself is not verified where it calls `ApplyConfiguration`, which runs the program's code.

## Queries

A query on `ctx.Orders` (or `ctx.Set<Order>()`) is LINQ over the table as it is when the query runs. `Queryable`'s
operators, and EF's `...Async` forms awaited where they are called, are read from LINQ to Objects' definitions
([Contracts for code without sources](library-contracts.md)). Each run reads the table afresh:
- its rows are in no order the database promises, unless the query orders them;
- no two have the same key, or the same value of a unique index;
- each passes the entity's query filters, unless the query says `IgnoreQueryFilters()`;
- strings are compared as the database compares them: an equivalence that equal strings satisfy, of which nothing
  else is known. SQL Server's default collation ignores case and trailing spaces, SQLite's does not: where the only
  providers the program names are SQLite and the in-memory one, and nothing sets a collation (`UseCollation`, a column
  type with `COLLATE`, `EF.Functions.Collate`), strings compare as `==` does, and a join on strings is read like one
  on integers. (This is of a database made from the model: one whose columns were given a collation elsewhere isn't
  seen);
- other code may have changed the table since the last run, so two runs needn't agree;
- comparisons of what may be null mean what they do in C#, as EF makes them by default. With SQL's null semantics
  (`UseRelationalNulls()`, anywhere in the program), `==` and `!=` where either side is null are unknown: SQL's
  unknown, which EF carries through a `!`, so nothing is known of whether such a row is kept. Other comparisons, and
  those against `null`, stay C#'s, which EF keeps.

So `Where`, `Count`, `Any` and `All` are exact, `SingleOrDefault(c => c.Email == email)` is proved to find at most one
row when `Email` has a unique index, and a row a query gives passes its predicate.

A query's lambdas are SQL, not C#: a null navigation or column there is a null, not a `NullReferenceException`. So
`m.Card!.Provider`, `m.StartedAt!.Value` and `m.Email!.Equals(email)` in them aren't checked for null: they aren't
verified as C#, and CSV1032 checks what EF translates. That holds in query syntax (`from m in ctx.Members join c in
ctx.Cards on ...`), and for a query started from a local that only its declaration sets, to a table's query or a
`?:` of two of the same table (`var members = all ? ctx.Members.IgnoreQueryFilters() : ctx.Members`). A query from a
parameter isn't: an `IQueryable<T>` passed in may be a list's `AsQueryable()`, where a null member throws. (In a final `Select` that EF runs on the client, a member of a
null navigation's entity is a materialized null: a non-nullable column of it makes EF throw.) A value converter's
lambdas (`HasConversion`) aren't given null, which EF doesn't convert. The rows a query gives aren't null, tracked or
not, so `await ctx.Members.SingleAsync(m => m.RowId == row)` gives one; that there is one is `Single`'s
precondition, which no code shows: the database decides. A query by key, `SingleOrDefaultAsync(m => m.RowId == row) ??
throw ...`, says it fails where there is none, and verifies, tracked or not. (A tracked query gives the instances the
context tracks, as the program left them; what the database matched is known of them only where the context tracked
none of the type before, or where the predicate reads only key or alternate key columns, which a tracked entity's are
its row's.) A property the configuration names (`Property`, `HasKey`, `HasAlternateKey`)
is a column, a get-only one too.

**Joins, groups and sets.** `Join`, `LeftJoin`, `GroupJoin` and `GroupBy` on a key that the database and .NET compare
alike (an integer, `bool`, an enum or a `Guid`, or one of those nullable; a string, where strings compare exactly; or a
tuple or anonymous type of them), and `Distinct`, `Union`, `Intersect`, `Except` and `Contains` of such values, are read
from their definitions: each pair has equal keys, a null key matches nothing (in SQL, and in LINQ to Objects), a left
join adds each row that matches none, with null for the other side, and a group holds the rows of its key. What these,
`SelectMany` or `Concat` give is in no order of their sources (SQL Server's hash join doesn't keep a row's matches
together, nor `GROUP BY` the order keys first appear in): the verifier reads it in any order. `ToDictionary`,
`ToLookup` and `ToHashSet`, made in memory from the rows, compare as .NET does. So an order joined
to its customer on the customer's key is proved to be paired with the customer who placed it, and to be one row at
most:

```csharp
var row = await db.Orders.AsNoTracking().Where(o => o.Id == id)
    .Join(db.Customers.AsNoTracking(), o => o.CustomerId, c => c.Id, (o, c) => new { Order = o, Customer = c })
    .SingleOrDefaultAsync(ct);
// row == null || row.Customer.Id == row.Order.CustomerId
```

**Tracking.** Read with `AsNoTracking()`, the rows are new objects, and so are what EF makes with them:
- a reference navigation not `Include`d is null; a collection not included is as the entity's constructor left it,
  empty where its initializer is an empty list (`= new List<Order>()`), null where there is none;
- an included reference is the row its foreign key names, and not null when the key can't be null; an included
  `List` (or `IList`, or another collection interface whose initializer makes a `List`) or `HashSet` holds only rows
  whose foreign key is this row's key. Each passes its type's query filters, unless the query ignores them. So does each level an
  `Include` path loads (`Include(o => o.Lines).ThenInclude(l => l.Product)`). Foreign keys are read as EF finds them:
  `HasOne(...).WithMany(...).HasForeignKey(...)` (or from `HasMany`), `[ForeignKey]`, or EF's convention (`CustomerId`
  for a navigation `Customer` to a key `Id`; the principal's name and its key's, for a collection with no navigation
  back), for a principal of one key property; a navigation the configuration names otherwise (a principal key, by
  name, `[InverseProperty]`) has no claim;
- a navigation to a type some `Include` path loads is not said null: EF sets the navigations of what it loads from one
  another (the order an included collection holds has its `Customer`);
- an `Include` by name, or a filtered one (`Include(c => c.Orders.Where(...))`), says nothing of navigations, nor does
  `AsNoTrackingWithIdentityResolution()`, whose navigations EF fixes up from the other rows it loads.

A column that no code writes once its object is made (no setter, an `init` one, or a private one its type assigns only
in its constructors) is as it was after an `await`, whatever the method lets out: only EF writes it after, when a
context that tracks the entity saves or reloads it. This assumes no other code's context saves or reloads the same
instance meanwhile.
If the method lets none of its entities out (to a field, to a call of the program's or a constructor, to a library call on
something not local, to a lambda other than a query's), no other code reaches them: an `await` leaves their columns,
concurrency tokens among them, as they were. Read with
tracking, a row whose key the context already tracks is that instance, with its values as they are in memory, which
may not be the database's: so what the query says of its rows is known only when the context tracked no entity of
that type before it. Then an included reference is the row its foreign key names (or null). When it tracked none of
the types the `Include` paths load either, every level is the database's, as without tracking; after the query, whether
the context tracks an entity of those types it didn't before isn't known. Of what else a context tracks, which EF
fixes navigations up from, nothing is said. `Count`, `Any` and the like, and projections of columns, return no entities and are always
exact. How many rows a query keeps doesn't depend on tracking either: a filter that compares every column of the key or
of a unique index to a value (`t.ExternalId == id`, whatever else it adds with `&&`) keeps one row at most, as the
database's rows are distinct by each. A nullable column doesn't count, since null may match many rows.

**Not read from the definitions:** on a database, those operators on other values (strings by the database's
collation, elsewhere than SQLite; dates and floating point, by the column's precision; entities, rows compared by every
column) compare as the database does: they are library calls, which say nothing of what they give. So is `RightJoin`:
EF Core applies the left side's query filters to the joined rows, which drops the right side's rows that match none.
And so are the `By` forms (`DistinctBy`...), `SequenceEqual`, `CountBy` and `AggregateBy`, which EF doesn't translate.
In a query's lambda, `Contains` of a list passed in compares as the database does too: strings by its collation.

**Query helpers.** A method that takes a query (`IQueryable<T>`) is translated: of the rows of the query passed in
(not null, where their type isn't nullable), only what its specification says is known. A private one of the same
file with no contract is read where it is awaited instead, on the query its caller passes (a table and Queryable's
and EF's operators): `Load(db.Items.Where(t => t.ExternalId == id))` is that query, ordered and listed as `Load` does.
Its body may declare locals, run statements (awaits among them), return early from an `if`, and set fields in a
`foreach` (each field it sets is some value after; an entity tracked stays tracked); every way ends in a `return`.
Its obligations are proved where it is verified. EF's
operators of the whole query (`Include`, `AsNoTracking`, `IgnoreQueryFilters`...) mean the same after a filter, an
order or a page as before them. A private method of the type without parameters that returns a query in one
expression (`IQueryable<Item> Items() => db.Items.Include(i => i.Owner)`, a table written once with its includes) is
read where a query is built on it. A query as a value is an object, not null; what it reads is read where it runs.
`EF.Property<T>(x, "Name")` is the column of that name: the class's property, or a shadow column's value, not known.
A query filter the verifier doesn't read (of a type it doesn't have, say) says nothing of the rows, as one left
out; the query is read all the same. The lambdas the model's builders take (`HasQueryFilter(x => ...)`,
`HasIndex(x => ...)`) are EF's to read, not run, and aren't verified as C#.
In a query's lambda, a subquery of a scalar correlated by the row
(`Owner = db.Owners.Where(o => o.Id == t.OwnerId).Select(o => o.Id).FirstOrDefault()`) is a value of the row not known.
`LoadAsync` of a query reads it, tracked: its rows are tracked from there on. A list `ToListAsync` (or LINQ's `ToList`)
made is the method's own: an `await` leaves its rows as they were, where the method gives it only to LINQ's operators.

**Each row of a list.** A list a query that keeps each row once makes (a filter, an order, a page) holds a different
object at each index, tracked or not. A `foreach` over such a list may call EF's `Add`, `Attach`, `Update`, `Remove` and
`Entry` and still read its elements, since those change no list but navigations. Each element the loop hasn't reached
yet keeps its tracking (an inferred invariant, kept where it holds), so `Remove` of each row a tracking query listed
finds the instance its context tracks. `Remove` of an entity the context tracks, whose navigations all lead to its
principals (a reference with its foreign key on it), changes only that entity's state.

A private method of one parameter, a list, that each of its calls passes the rows a tracked query gives, awaited
there (`await Remove(await db.Items.Where(...).ToListAsync())`), on a context of this object's (a `readonly` field,
or a primary constructor's parameter its code doesn't assign), begins knowing what such a list is: its rows are
different objects, each tracked by that context, as nothing runs between the query and the call. Its `foreach` may
call EF's tracker too, as above.

**Compiled queries.** A `static readonly` field made by `EF.CompileQuery`, called in its own file, that gives a value
(`FirstOrDefault`, `Single`, `Count`, `Any`...) is the query its lambda writes, read and checked as one written there.
One that gives a sequence, `EF.CompileAsyncQuery`'s, and one declared in another file are library calls.

**Reported:**
- **CSV1031**, keeping rows by their place in an order the database doesn't fix: `First`, `Last`, `ElementAt`, `Take`
  and `Skip` need the query ordered by a key or a unique index (`OrderBy(o => o.Placed).ThenBy(o => o.Id)`), or at most
  one row that matches (`FirstOrDefault(o => o.Id == id)`, proved; a `Select` of the rows keeps their count, so
  `Where(o => o.Id == id).Select(o => o.Number).FirstOrDefault()` too).
- **CSV1032**, what EF can't translate to SQL: in a query's lambda, what depends on the row may read columns and
  navigations and call what EF translates (operators, string, `Math` and date members, LINQ over navigations and over
  lists passed in); a method of the program, or a property computed in C# or `[NotMapped]`, makes EF throw when the
  query runs. What doesn't depend on the row is evaluated before the query is sent, so it may call anything, and so
  may the final `Select`, which runs on the client. And an `Include` path that comes back to a type on it
  (`Include(o => o.Customer).ThenInclude(c => c.Orders)`) in a query without tracking: EF refuses it.

## The change tracker

A context's tracked entities, their states (`EntityState`), its unsaved changes and its transaction are ghost state
the verifier follows from call to call: `Add`, `Attach`, `Update`, `Remove`, `Entry(e).State = ...`, `Find`,
`SaveChanges`, `Entry(e).Reload()`, `ChangeTracker.Clear()`, and a write of a tracked entity's field (which makes it
modified). A context made here (`new`, or `IDbContextFactory.CreateDbContext`) tracks nothing; one passed in may track
anything.

Queries read the database, not the changes a context holds. `ctx.Orders.Local` is what it holds: each entity of the
type it tracks and doesn't delete (unchanged, modified or added), once, as it is when the view is read, and LINQ over
it is read from LINQ to Objects' definitions. So after `Add(o)` on a new context, `Local` holds `o` and nothing else;
after `Remove(o)` of an added `o`, it is empty.

**Reported:**
- **CSV1033**, the tracker misused:
  - `Attach`, `Update`, `Add` (of a key that is set), `Remove` or `Entry(e).State = ...` where the context may track
    another instance with the same key: EF throws. A key EF generates (an integer key still 0) never clashes; of an entity passed in, the caller says so
    (`Spec.Requires(posting.Id == 0)`).
  - a write of a key's or an alternate key's property of an entity a context may track (unless added): EF throws where
    it detects the change. A new entity's, and a constructor's, are not tracked.
  - `Update` of an entity whose navigations hold something: EF marks what they hold as modified too, and writes every
    column of each. Update the one entity (`Entry(e).State = EntityState.Modified`), or load the graph tracked.
  - a context used after `SaveChanges` failed on it, or after its transaction rolled back (or was disposed
    uncommitted): what it tracks is no longer what the database holds.
  - `SaveChanges` writing an entity that `ExecuteUpdate` or `ExecuteDelete` on its table may have changed since it was
    read: reload it first.
- **CSV1034**, concurrency tokens:
  - `Attach`, `Update` or `Entry(e).State = Modified` of an entity this context read, whose token was changed since:
    EF would check the row against the new value. Mark it first, then change it.
  - a write of a row version, which the database sets (and does, at each `SaveChanges` that writes the entity).

## Transactions

- **CSV1035:**
  - `BeginTransaction` where one may be open: EF throws. Code that joins the caller's transaction or begins its own
    (`db.Database.CurrentTransaction == null ? await db.Database.BeginTransactionAsync() : null`) verifies.
  - `Commit` with changes not saved: they aren't in the transaction.
  - a second `SaveChanges` on a context outside a transaction: if it fails, what the first saved stays.

## One operation at a time

A context isn't thread safe, and EF throws when two of its operations overlap.

- **CSV1036:**
  - an asynchronous operation on a context (a query, `SaveChangesAsync`, `BeginTransactionAsync`...) not awaited where
    it starts: `Task.WhenAll` of two queries on one context is reported. One returned by a method that isn't async is
    not: it is the caller's to await.
  - a context from outside used in code that runs alongside (`Task.Run`, `Task.Factory.StartNew`, `Parallel`,
    `ThreadPool`, a `Thread`). Each such task makes its own (`IDbContextFactory`).

## Across calls

A failed save, a rollback, entities read and the tokens read, a bulk update's stale rows and saves outside a
transaction are each method's own record, none at its start: what a caller did to a context passed in isn't seen. A
call of the program's adds what the callee's code (and its callees') may do to a context:
- break it: it rolls back, or catches a failed save or commit without throwing again;
- save outside the transaction the caller has open;
- change rows the caller tracks, with `ExecuteUpdate` or `ExecuteDelete`.

So a helper that saves and lets a failure out leaves the context usable, one that swallows the failure doesn't, and
the caller's own save after a helper's is a second one outside a transaction.

## Limits

- What the database does with a query (its SQL) is not proved: the definitions are trusted, and checked against EF on
  SQLite and on SQL Server (`tests/CsVerify.EfTests`, `EfConformanceTests`): each rule above is run there, and where
  the two differ (collation, overflow in a query, overlapping operations), the model claims only what both do. Joins,
  groups and set operators are checked there against LINQ to Objects.
- Raw SQL (`FromSql`, `ExecuteSql`) is a library call.
- An `ICollection` navigation EF makes a `HashSet` (one without an initializer) has no claim: what is read through
  `ICollection` isn't followed to the set it is. Declare it `HashSet<T>` to have one.
- String members inside a query (`Contains`, `ToUpper`, `Length`...) translate, but their values are unknown: SQL
  Server's and .NET's differ.
