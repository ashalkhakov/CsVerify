using CsVerify;

namespace Samples
{
    // Object-oriented code, verified modularly with behavioural subtyping: a call through a base type is checked
    // against the base's contract, and every override is checked against it too (it may require less and promise
    // more, never the other way round).

    /// <summary>A shape. Area is a [Pure] query: one function for every override, usable in specifications.</summary>
    public abstract class Shape
    {
        [Pure] public abstract long Area();
    }

    /// <summary>The contracts of Shape's abstract members (the Code Contracts pattern; erased from builds).</summary>
    [ContractClassFor(typeof(Shape))]
    internal abstract class ShapeContract : Shape
    {
        public override long Area()
        {
            Spec.Ensures((long r) => r >= 0);
            return 0;
        }
    }

    /// <summary>An immutable shape: its invariant is proved by the constructor and holds of every Square after.</summary>
    public sealed class Square : Shape
    {
        public readonly int Side;

        [Invariant, Pure] public bool Valid() => Side >= 0;

        public Square(int side)
        {
            Spec.Requires(side >= 0);
            Spec.Ensures(Side == side);
            Side = side;
        }

        [Pure] public override long Area() => (long)Side * Side;
    }

    public sealed class Rectangle : Shape
    {
        public readonly int Width, Height;

        [Invariant, Pure] public bool Valid() => Width >= 0 && Height >= 0;

        public Rectangle(int width, int height)
        {
            Spec.Requires(width >= 0 && height >= 0);
            Spec.Ensures(Width == width && Height == height);
            Width = width;
            Height = height;
        }

        [Pure] public override long Area() => (long)Width * Height;
    }

    /// <summary>
    /// An account: the abstract interface of a mutable object. Each operation changes only the account itself
    /// (Spec.Modifies), so a call on one account, whatever its class, leaves every other object as it was.
    /// </summary>
    public abstract class BankAccount
    {
        [Pure] public abstract int Balance { get; }

        public abstract void Deposit(int amount);

        /// <summary>Withdraws if the account allows it; says whether it did.</summary>
        public abstract bool TryWithdraw(int amount);
    }

    [ContractClassFor(typeof(BankAccount))]
    internal abstract class AccountContract : BankAccount
    {
        public override int Balance
        {
            get
            {
                Spec.Reads(ObjSet.Of(this)); // a balance depends on its own account only
                return 0;
            }
        }

        public override void Deposit(int amount)
        {
            Spec.Requires(amount >= 0);
            Spec.Modifies(ObjSet.Of(this));
            Spec.Ensures(Balance == Spec.Old(Balance) + amount);
        }

        public override bool TryWithdraw(int amount)
        {
            Spec.Requires(amount >= 0);
            Spec.Modifies(ObjSet.Of(this));
            Spec.Ensures((bool ok) => ok ? Balance == Spec.Old(Balance) - amount : Balance == Spec.Old(Balance));
            return false;
        }
    }

    /// <summary>An account that never goes below zero.</summary>
    public class Checking : BankAccount
    {
        protected int Funds;

        public Checking(int initial)
        {
            Spec.Requires(initial >= 0);
            Spec.Ensures(Funds == initial);
            Funds = initial;
        }

        /// <summary>Sealed: Funds is the balance of every kind of Checking, so this body defines the query for them.</summary>
        [Pure] public sealed override int Balance => Funds;

        public override void Deposit(int amount)
        {
            Spec.Modifies(ObjSet.Of(this));
            Funds = checked(Funds + amount); // a deposit that would overflow throws
        }

        public override bool TryWithdraw(int amount)
        {
            Spec.Modifies(ObjSet.Of(this));
            if (amount > Funds) return false;
            Funds -= amount;
            return true;
        }
    }

    /// <summary>An account that may go down to -Limit: built on Checking (base(...)), and it allows more withdrawals.</summary>
    public sealed class Overdraft : Checking
    {
        public readonly int Limit;

        public Overdraft(int initial, int limit) : base(initial)
        {
            Spec.Requires(initial >= 0 && limit >= 0);
            Spec.Ensures(Funds == initial && Limit == limit);
            Limit = limit;
        }

        public override bool TryWithdraw(int amount)
        {
            Spec.Modifies(ObjSet.Of(this));
            if ((long)Funds - amount < -(long)Limit) return false;
            Funds -= amount;
            return true;
        }
    }

    public static class Oop
    {
        /// <summary>The total area of some shapes: Area's contract, whichever shapes they are.</summary>
        public static long TotalArea(Shape[] shapes)
        {
            Spec.Requires(Spec.Forall(0, shapes.Length, i => shapes[i] != null));
            Spec.Ensures((long r) => r >= 0);
            long total = 0;
            for (int i = 0; i < shapes.Length; i++)
            {
                Spec.Invariant(0 <= i && i <= shapes.Length && total >= 0);
                total = checked(total + shapes[i].Area());
            }
            return total;
        }

        /// <summary>Moves money between two accounts of any kind; the sum is unchanged either way.</summary>
        public static bool Transfer(BankAccount from, BankAccount to, int amount)
        {
            Spec.Requires(from != to && amount >= 0);
            Spec.Modifies(ObjSet.Of(from).Add(to));
            Spec.Ensures((bool ok) => (long)from.Balance + to.Balance == (long)Spec.Old(from.Balance) + Spec.Old(to.Balance));
            if (!from.TryWithdraw(amount)) return false;
            to.Deposit(amount);
            return true;
        }

        /// <summary>A square's area through a Shape reference: the object is known to be a Square, whose Area runs.</summary>
        public static long Nine()
        {
            Spec.Ensures((long r) => r == 9);
            Shape s = new Square(3);
            return s.Area();
        }

        public static long Demo()
        {
            var shapes = new Shape[] { new Square(3), new Rectangle(2, 5) };
            long area = TotalArea(shapes);                       // 19
            var checking = new Checking(100);
            var overdraft = new Overdraft(0, 50);
            bool first = Transfer(overdraft, checking, 30);      // allowed: overdraft goes to -30
            bool second = Transfer(overdraft, checking, 30);     // refused: it would be -60
            return checked(area * 10000 + checking.Balance * 10 + (first ? 1 : 0) + (second ? 2 : 0) + Nine() * 100000000L);
        }
    }
}
