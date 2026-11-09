# Entity Framework Core

For a program that references EF Core, the verifier reads queries on a `DbContext` as what the database runs, and
checks that the context is used as EF requires: its change tracker, transactions and concurrency tokens, and one
operation at a time. Nothing needs to be written for this: the model comes from the program's own EF configuration.
`samples/EntityFramework` has a program that verifies and one with a bug in each method.

## The model

Read from the sources, as EF reads them:
- **Entity types:** a context's `DbSet<T>` properties, the types its configuration names, and what their navigations
  lead to.
- **Keys:** `[Key]`, `HasKey(x => x.P)` or `HasKey(x => new { x.A, x.B })`, or EF's convention (`Id`, or the type's
  name and `Id`).
- **Unique values:** `[Index(..., IsUnique = true)]`, `HasIndex(...).IsUnique()`, `HasAlternateKey(...)`.
- **Concurrency tokens:** `[ConcurrencyCheck]`, `IsConcurrencyToken()`; row versions: `[Timestamp]`, `IsRowVersion()`.
- **Query filters:** `HasQueryFilter(x => ...)`.
- **Navigations:** properties of an entity type, or of a collection of one.

Fluent configuration is read in `OnModelCreating` and in `IEntityTypeConfiguration<T>.Configure`.

## Queries

A query on `ctx.Orders` (or `ctx.Set<Order>()`) is LINQ over the table as it is when the query runs. `Queryable`'s
operators, and EF's `...Async` forms awaited where they are called, are read from LINQ to Objects' definitions
([Contracts for code without sources](library-contracts.md)). Each run reads the table afresh:
- its rows are in no order the database promises, unless the query orders them;
- no two have the same key, or the same value of a unique index;
- each passes the entity's query filters, unless the query says `IgnoreQueryFilters()`;
- strings are compared as the database compares them: an equivalence that equal strings satisfy, of which nothing
  else is known. SQL Server's default collation ignores case and trailing spaces, SQLite's does not;
- other code may have changed the table since the last run, so two runs needn't agree;
- comparisons of what may be null mean what they do in C#, as EF makes them by default. With SQL's null semantics
  (`UseRelationalNulls()`, anywhere in the program), `==` and `!=` where either side is null are unknown: SQL's
  unknown, which EF carries through a `!`, so nothing is known of whether such a row is kept. Other comparisons, and
  those against `null`, stay C#'s, which EF keeps.

So `Where`, `Count`, `Any` and `All` are exact, `SingleOrDefault(c => c.Email == email)` is proved to find at most one
row when `Email` has a unique index, and a row a query gives passes its predicate.

**Joins.** `Join` and `LeftJoin` on a key that the database and .NET compare alike (an integer, `bool`, an enum or a
`Guid`, or one of those nullable) are read from their definitions: each pair has equal keys, a null key matches
nothing (in SQL, and in LINQ to Objects), and a left join adds each row that matches none, with null for the other
side. What a join, `SelectMany` or `Concat` gives is in no order of its sources
(SQL Server's hash join doesn't keep a row's matches together): the verifier reads it in any order. So an order joined
to its customer on the customer's key is proved to be paired with the customer who placed it, and to be one row at
most:

```csharp
var row = await db.Orders.AsNoTracking().Where(o => o.Id == id)
    .Join(db.Customers.AsNoTracking(), o => o.CustomerId, c => c.Id, (o, c) => new { Order = o, Customer = c })
    .SingleOrDefaultAsync(ct);
// row == null || row.Customer.Id == row.Order.CustomerId
```

**Tracking.** Read with `AsNoTracking()`, the rows are new objects, and a navigation not `Include`d is null. If the
method lets none of its entities out (to a field, to a call of the program's or a constructor, to a library call on
something not local, to a lambda other than a query's), no other code reaches them: an `await` leaves their columns,
concurrency tokens among them, as they were. Read with
tracking, a row whose key the context already tracks is that instance, with its values as they are in memory, which
may not be the database's: so what the query says of its rows is known only when the context tracked no entity of
that type before it. `Count`, `Any` and the like, and projections of columns, return no entities and are always
exact.

**Not read from the definitions:** on a database, operators that compare values for equality (`Distinct`, `GroupBy`,
`GroupJoin`, `Union`, `Intersect`, `Except`, `Contains`, `ToDictionary`), and joins on other keys (strings, by the
database's collation; dates and floating point, by the column's precision), compare as the database does. They are library calls, which say nothing of what they give. So is `RightJoin`: EF Core applies the left side's
query filters to the joined rows, which drops the right side's rows that match none.

**Reported:**
- **CSV1031**, keeping rows by their place in an order the database doesn't fix: `First`, `Last`, `ElementAt`, `Take`
  and `Skip` need the query ordered by a key or a unique index (`OrderBy(o => o.Placed).ThenBy(o => o.Id)`), or at most
  one row that matches (`FirstOrDefault(o => o.Id == id)`, proved).
- **CSV1032**, what EF can't translate to SQL: in a query's lambda, what depends on the row may read columns and
  navigations and call what EF translates (operators, string, `Math` and date members, LINQ over navigations and over
  lists passed in); a method of the program, or a property computed in C# or `[NotMapped]`, makes EF throw when the
  query runs. What doesn't depend on the row is evaluated before the query is sent, so it may call anything, and so
  may the final `Select`, which runs on the client.

## The change tracker

A context's tracked entities, their states (`EntityState`), its unsaved changes and its transaction are ghost state
the verifier follows from call to call: `Add`, `Attach`, `Update`, `Remove`, `Entry(e).State = ...`, `Find`,
`SaveChanges`, `Entry(e).Reload()`, `ChangeTracker.Clear()`, and a write of a tracked entity's field (which makes it
modified). A context made here (`new`, or `IDbContextFactory.CreateDbContext`) tracks nothing; one passed in may track
anything.

**Reported:**
- **CSV1033**, the tracker misused:
  - `Attach`, `Update`, `Add` (of a key that is set), `Remove` or `Entry(e).State = ...` where the context may track
    another instance with the same key: EF throws. A key EF generates (an integer key still 0) never clashes.
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
    it starts, or returned by a method that isn't async (which leaves it to the caller): `Task.WhenAll` of two queries
    on one context is reported.
  - a context from outside used in code that runs alongside (`Task.Run`, `Task.Factory.StartNew`, `Parallel`,
    `ThreadPool`, a `Thread`). Each such task makes its own (`IDbContextFactory`).

## What is checked within a method

A failed save, a rollback, entities read and the tokens read, a bulk update's stale rows and saves outside a
transaction are each method's own record: none at its start, and calls don't change them. So these rules hold within
a method, not across calls: a context a caller broke, or a save a callee made, is not seen.

## Limits

- What the database does with a query (its SQL) is not proved: the definitions are trusted, and checked against EF on
  SQLite and on SQL Server (`tests/CsVerify.EfTests`, `EfConformanceTests`): each rule above is run there, and where
  the two differ (collation, overflow in a query, overlapping operations), the model claims only what both do. Joins
are checked there against LINQ to Objects, which matches no null key, as SQL doesn't.
- A concurrency token is followed only for an entity's first one.
- `Find` with a composite key, raw SQL (`FromSql`, `ExecuteSql`), compiled queries, owned types and inheritance mapping
  are library calls.
- String members inside a query (`Contains`, `ToUpper`, `Length`...) translate, but their values are unknown: SQL
  Server's and .NET's differ.
