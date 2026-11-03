using CsVerify;

namespace Samples
{
    // Permissions to single fields (Viper's acc(o.f)): code may hold one field of an object while other code holds
    // another. A call that gets one field changes only that field; the rest of the object stays known.

    /// <summary>A particle: where it is and how fast it goes, written by different code.</summary>
    [Owned]
    public sealed class Particle
    {
        public int Pos;
        public int Speed;
    }

    public static class FieldPermissions
    {
        /// <summary>Moves a particle: needs its position only (the speed is read, which needs nothing).</summary>
        public static void Move(Particle p, int by)
        {
            Spec.Requires(Spec.Acc(p, nameof(Particle.Pos)) && -1000 <= by && by <= 1000 && -1000000 <= p.Pos && p.Pos <= 1000000);
            Spec.Ensures(Spec.Acc(p, nameof(Particle.Pos)) && p.Pos == Spec.Old(p.Pos) + by);
            p.Pos += by;
        }

        /// <summary>Speeds up: its speed only.</summary>
        public static void Accelerate(Particle p)
        {
            Spec.Requires(Spec.Acc(p, nameof(Particle.Speed)) && p.Speed < 1000);
            Spec.Ensures(Spec.Acc(p, nameof(Particle.Speed)) && p.Speed == Spec.Old(p.Speed) + 1);
            p.Speed++;
        }

        /// <summary>The two fields of one object, given apart: they make the whole object.</summary>
        public static void Reset(Particle p)
        {
            Spec.Requires(Spec.Acc(p, nameof(Particle.Pos)) && Spec.Acc(p, nameof(Particle.Speed)));
            Spec.Ensures(Spec.Acc(p) && p.Pos == 0 && p.Speed == 0);
            p.Pos = 0;
            p.Speed = 0;
        }

        /// <summary>A predicate over one field: positions that are not negative.</summary>
        [Predicate]
        public static bool Ahead(Particle p) => Spec.Acc(p, nameof(Particle.Pos)) && p.Pos >= 0;

        /// <summary>
        /// The whole object in hand (its view): giving out the position keeps the speed, and the position comes back,
        /// so the object is whole again (it could be handed over as a view).
        /// </summary>
        public static int Step(Particle p, ref Own<Particle> view)
        {
            Spec.Requires(view.Obj.Value == p && p.Pos == 0 && p.Speed == 3);
            Spec.Ensures((int r) => r == 3 && p.Pos == 3 && p.Speed == 4);
            Move(p, p.Speed);                 // gives Pos; Speed stays known
            Spec.Assert(p.Speed == 3);
            Accelerate(p);                     // gives Speed; Pos stays known
            Spec.Assert(p.Pos == 3);
            Spec.Fold(Ahead(p));
            Accelerate(p);
            Spec.Unfold(Ahead(p));
            p.Speed = 4;                       // and the speed again (it came back)
            Touch(ref view);                   // whole again: the view can go
            return p.Pos;
        }

        private static void Touch(ref Own<Particle> view) { }
    }
}
