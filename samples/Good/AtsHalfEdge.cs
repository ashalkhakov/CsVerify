using CsVerify;

namespace Samples
{
    // A port of ATS-playground/half-edge-mesh (Artyom Shalkhakov, 2014-2015): half-edge collapse and split. In ATS a
    // mesh is a region (RGN(l0)); its half-edges, faces and vertices are region pointers, which may alias freely and
    // are writable because the region contains them (vsubw_p). That they point into the region was taken on trust
    // (__trustme in rgnptr_make_some; the accessors used $UN.ptr0_vtake).
    //
    // Here the region is a predicate over the mesh and its arrays (structure of arrays; a region pointer is an index,
    // hedge_none is -1), and "no dangling region pointers" is part of the predicate: every next, prev, twin, vtx and
    // face is in range, and collapse and split are proved to keep it so. Collapse deactivates the half-edge's face and
    // split activates it again.

    /// <summary>A mesh: per half-edge its next, previous and twin half-edges, its vertex and its face; per face, active.</summary>
    [Owned]
    public sealed class HMesh
    {
        public int[] Next, Prev, Twin, Vtx, Face;
        public bool[] Active;
        public int Verts;

        public HMesh(int[] next, int[] prev, int[] twin, int[] vtx, int[] face, bool[] active, int verts)
        {
            Spec.Ensures(Next == next && Prev == prev && Twin == twin && Vtx == vtx && Face == face && Active == active && Verts == verts);
            Next = next; Prev = prev; Twin = twin; Vtx = vtx; Face = face; Active = active; Verts = verts;
        }
    }

    public static class AtsHalfEdge
    {
        public const int None = -1; // hedge_none

        /// <summary>
        /// RGN(l0) with every region pointer in it: the arrays (one cell per half-edge or face, all held), and every
        /// half-edge's links in range (a twin may be none).
        /// </summary>
        [Predicate]
        public static bool Mesh(HMesh m) =>
            m != null && Spec.Acc(m) &&
            m.Next != null && m.Prev != null && m.Twin != null && m.Vtx != null && m.Face != null && m.Active != null &&
            m.Prev.Length == m.Next.Length && m.Twin.Length == m.Next.Length && m.Vtx.Length == m.Next.Length &&
            m.Face.Length == m.Next.Length && m.Verts > 0 && m.Active.Length > 0 &&
            Spec.Acc(m.Next) && Spec.Acc(m.Prev) && Spec.Acc(m.Twin) && Spec.Acc(m.Vtx) && Spec.Acc(m.Face) && Spec.Acc(m.Active) &&
            Spec.Forall(0, m.Next.Length, h =>
                0 <= m.Next[h] && m.Next[h] < m.Next.Length && 0 <= m.Prev[h] && m.Prev[h] < m.Next.Length &&
                None <= m.Twin[h] && m.Twin[h] < m.Next.Length &&
                0 <= m.Vtx[h] && m.Vtx[h] < m.Verts && 0 <= m.Face[h] && m.Face[h] < m.Active.Length);

        // ------------------------------------------------------------------------------------------ sizes
        // (functions over the predicate: Viper's unfolding in a function)

        [Pure]
        public static int Hedges(HMesh m)
        {
            Spec.Requires(Mesh(m));
            Spec.Ensures((int r) => r >= 0);
            Spec.Unfold(Mesh(m));
            return m.Next.Length;
        }

        [Pure]
        public static int Verts(HMesh m)
        {
            Spec.Requires(Mesh(m));
            Spec.Ensures((int r) => r > 0);
            Spec.Unfold(Mesh(m));
            return m.Verts;
        }

        [Pure]
        public static int Faces(HMesh m)
        {
            Spec.Requires(Mesh(m));
            Spec.Ensures((int r) => r > 0);
            Spec.Unfold(Mesh(m));
            return m.Active.Length;
        }

        // ------------------------------------------------------------------------------------------ accessors
        // (.next, .prev, .twin, .vtx, .face, .active: reads, total on a half-edge of the mesh, so functions)

        [Pure]
        public static int NextOf(HMesh m, int h)
        {
            Spec.Requires(Mesh(m) && 0 <= h && h < Hedges(m));
            Spec.Ensures((int r) => 0 <= r && r < m.Next.Length);
            Spec.Unfold(Mesh(m));
            return m.Next[h];
        }

        [Pure]
        public static int PrevOf(HMesh m, int h)
        {
            Spec.Requires(Mesh(m) && 0 <= h && h < Hedges(m));
            Spec.Ensures((int r) => 0 <= r && r < m.Next.Length);
            Spec.Unfold(Mesh(m));
            return m.Prev[h];
        }

        /// <summary>twin_get: partial, may be none.</summary>
        [Pure]
        public static int TwinOf(HMesh m, int h)
        {
            Spec.Requires(Mesh(m) && 0 <= h && h < Hedges(m));
            Spec.Ensures((int r) => None <= r && r < m.Next.Length);
            Spec.Unfold(Mesh(m));
            return m.Twin[h];
        }

        [Pure]
        public static int VtxOf(HMesh m, int h)
        {
            Spec.Requires(Mesh(m) && 0 <= h && h < Hedges(m));
            Spec.Ensures((int r) => 0 <= r && r < m.Verts);
            Spec.Unfold(Mesh(m));
            return m.Vtx[h];
        }

        [Pure]
        public static int FaceOf(HMesh m, int h)
        {
            Spec.Requires(Mesh(m) && 0 <= h && h < Hedges(m));
            Spec.Ensures((int r) => 0 <= r && r < m.Active.Length);
            Spec.Unfold(Mesh(m));
            return m.Face[h];
        }

        /// <summary>face_active_get (false for a face that is not one).</summary>
        [Pure]
        public static bool IsActive(HMesh m, int f)
        {
            Spec.Requires(Mesh(m));
            Spec.Unfold(Mesh(m));
            return 0 <= f && f < m.Active.Length && m.Active[f];
        }

        /// <summary>twin_set.</summary>
        public static void SetTwin(HMesh m, int h, int g)
        {
            Spec.Requires(Mesh(m) && 0 <= h && h < Hedges(m) && None <= g && g < Hedges(m));
            Spec.Ensures(Mesh(m) && Hedges(m) == Spec.Old(Hedges(m)) && Verts(m) == Spec.Old(Verts(m)) && Faces(m) == Spec.Old(Faces(m)));
            Spec.Ensures(Spec.Forall(0, Hedges(m), k => FaceOf(m, k) == Spec.Old(FaceOf(m, k))) && Spec.Forall(0, Faces(m), f => IsActive(m, f) == Spec.Old(IsActive(m, f))));
            Spec.Unfold(Mesh(m));
            m.Twin[h] = g;
            Spec.Fold(Mesh(m));
        }

        /// <summary>vtx_set.</summary>
        public static void SetVtx(HMesh m, int h, int v)
        {
            Spec.Requires(Mesh(m) && 0 <= h && h < Hedges(m) && 0 <= v && v < Verts(m));
            Spec.Ensures(Mesh(m) && Hedges(m) == Spec.Old(Hedges(m)) && Verts(m) == Spec.Old(Verts(m)) && Faces(m) == Spec.Old(Faces(m)));
            Spec.Ensures(Spec.Forall(0, Hedges(m), k => FaceOf(m, k) == Spec.Old(FaceOf(m, k))) && Spec.Forall(0, Faces(m), f => IsActive(m, f) == Spec.Old(IsActive(m, f))));
            Spec.Unfold(Mesh(m));
            m.Vtx[h] = v;
            Spec.Fold(Mesh(m));
        }

        /// <summary>face_active_set: only face f changes.</summary>
        public static void SetActive(HMesh m, int f, bool active)
        {
            Spec.Requires(Mesh(m) && 0 <= f && f < Faces(m));
            Spec.Ensures(Mesh(m) && Hedges(m) == Spec.Old(Hedges(m)) && Verts(m) == Spec.Old(Verts(m)) && Faces(m) == Spec.Old(Faces(m)) && IsActive(m, f) == active);
            Spec.Ensures(Spec.Forall(0, Hedges(m), k => FaceOf(m, k) == Spec.Old(FaceOf(m, k))) && Spec.Forall(0, Faces(m), k => k != f ? IsActive(m, k) == Spec.Old(IsActive(m, k)) : true));
            Spec.Unfold(Mesh(m));
            m.Active[f] = active;
            Spec.Fold(Mesh(m));
        }

        // ------------------------------------------------------------------------------------------ operations

        /// <summary>edge: do h and g run between the same two vertices, in opposite directions?</summary>
        [Pure]
        public static bool Edge(HMesh m, int h, int g)
        {
            Spec.Requires(Mesh(m) && 0 <= h && h < Hedges(m) && 0 <= g && g < Hedges(m));
            return VtxOf(m, h) == VtxOf(m, NextOf(m, g)) && VtxOf(m, g) == VtxOf(m, NextOf(m, h));
        }

        /// <summary>
        /// loop: gives every half-edge around a vertex the vertex a, walking with h (starting at the vertex) and g
        /// (ending at it) in the two directions, across twins, until both walks end or meet. As in ATS, it need not end
        /// on a broken mesh (it is not a total function): what is proved is what holds if it does.
        /// </summary>
        private static void Loop(HMesh m, int a, int h, int g)
        {
            Spec.Requires(Mesh(m) && 0 <= a && a < Verts(m) && None <= h && h < Hedges(m) && None <= g && g < Hedges(m));
            Spec.Ensures(Mesh(m) && Hedges(m) == Spec.Old(Hedges(m)) && Verts(m) == Spec.Old(Verts(m)) && Faces(m) == Spec.Old(Faces(m)));
            Spec.Ensures(Spec.Forall(0, Hedges(m), k => FaceOf(m, k) == Spec.Old(FaceOf(m, k))) && Spec.Forall(0, Faces(m), f => IsActive(m, f) == Spec.Old(IsActive(m, f))));
            while (h != None || g != None)
            {
                Spec.Invariant(Mesh(m) && Hedges(m) == Spec.Old(Hedges(m)) && Verts(m) == Spec.Old(Verts(m)) && Faces(m) == Spec.Old(Faces(m)));
                Spec.Invariant(None <= h && h < Hedges(m) && None <= g && g < Hedges(m) && 0 <= a && a < Verts(m));
                Spec.Invariant(Spec.Forall(0, Hedges(m), k => FaceOf(m, k) == Spec.Old(FaceOf(m, k))) && Spec.Forall(0, Faces(m), f => IsActive(m, f) == Spec.Old(IsActive(m, f))));
                if (h != None)
                {
                    SetVtx(m, h, a);
                    if (g != None)
                    {
                        int nextg = NextOf(m, g);
                        SetVtx(m, nextg, a);
                        if (Edge(m, PrevOf(m, h), nextg)) return; // the walks met
                        int th = TwinOf(m, PrevOf(m, h));
                        g = TwinOf(m, NextOf(m, g));
                        h = th;
                    }
                    else
                    {
                        h = TwinOf(m, PrevOf(m, h));
                    }
                }
                else
                {
                    int nextg = NextOf(m, g);
                    SetVtx(m, nextg, a);
                    g = TwinOf(m, nextg);
                }
            }
        }

        /// <summary>collapse's twinize: h's twin (if any) and g become each other's twins; returns g.</summary>
        private static int TwinizeCollapse(HMesh m, int h, int g)
        {
            Spec.Requires(Mesh(m) && 0 <= h && h < Hedges(m) && None <= g && g < Hedges(m));
            Spec.Ensures((int r) => r == g && Mesh(m) && Hedges(m) == Spec.Old(Hedges(m)) && Verts(m) == Spec.Old(Verts(m)) && Faces(m) == Spec.Old(Faces(m)));
            Spec.Ensures(Spec.Forall(0, Hedges(m), k => FaceOf(m, k) == Spec.Old(FaceOf(m, k))) && Spec.Forall(0, Faces(m), f => IsActive(m, f) == Spec.Old(IsActive(m, f))));
            int t = TwinOf(m, h);
            if (t != None)
            {
                SetTwin(m, t, g);
                if (g != None) SetTwin(m, g, t);
            }
            else if (g != None) SetTwin(m, g, None);
            return g;
        }

        /// <summary>
        /// collapse: removes the edge of h. Its face (and its twin's, if any) goes inactive, the twins across the
        /// removed triangles are joined, and the vertices around are merged into h's next one.
        /// </summary>
        public static void Collapse(HMesh m, int h)
        {
            Spec.Requires(Mesh(m) && 0 <= h && h < Hedges(m));
            Spec.Ensures(Mesh(m) && Hedges(m) == Spec.Old(Hedges(m)) && Verts(m) == Spec.Old(Verts(m)) && Faces(m) == Spec.Old(Faces(m)));
            Spec.Ensures(!IsActive(m, Spec.Old(FaceOf(m, h))));
            Spec.Ensures(Spec.Forall(0, Hedges(m), k => FaceOf(m, k) == Spec.Old(FaceOf(m, k))));
            int faceh = FaceOf(m, h);
            SetActive(m, faceh, false);
            int h1 = TwinizeCollapse(m, NextOf(m, h), TwinOf(m, PrevOf(m, h)));
            int g1 = None;
            int g = TwinOf(m, h);
            if (g != None)
            {
                SetActive(m, FaceOf(m, g), false);
                g1 = TwinizeCollapse(m, PrevOf(m, g), TwinOf(m, NextOf(m, g)));
            }
            Loop(m, VtxOf(m, NextOf(m, h)), h1, g1);
        }

        /// <summary>split's twinize: h's twin (if any) gets h back as its twin; returns that twin.</summary>
        private static int TwinizeSplit(HMesh m, int h)
        {
            Spec.Requires(Mesh(m) && 0 <= h && h < Hedges(m));
            Spec.Ensures((int r) => None <= r && r < Hedges(m) && Mesh(m) && Hedges(m) == Spec.Old(Hedges(m)) && Verts(m) == Spec.Old(Verts(m)) && Faces(m) == Spec.Old(Faces(m)));
            Spec.Ensures(Spec.Forall(0, Hedges(m), k => FaceOf(m, k) == Spec.Old(FaceOf(m, k))) && Spec.Forall(0, Faces(m), f => IsActive(m, f) == Spec.Old(IsActive(m, f))));
            int g = TwinOf(m, h);
            if (g != None) SetTwin(m, g, h);
            return g;
        }

        /// <summary>split: the inverse of collapse; h's face (and its twin's) comes back.</summary>
        public static void Split(HMesh m, int h)
        {
            Spec.Requires(Mesh(m) && 0 <= h && h < Hedges(m));
            Spec.Ensures(Mesh(m) && Hedges(m) == Spec.Old(Hedges(m)) && Verts(m) == Spec.Old(Verts(m)) && Faces(m) == Spec.Old(Faces(m)));
            Spec.Ensures(IsActive(m, Spec.Old(FaceOf(m, h))));
            Spec.Ensures(Spec.Forall(0, Hedges(m), k => FaceOf(m, k) == Spec.Old(FaceOf(m, k))));
            int faceh = FaceOf(m, h);
            SetActive(m, faceh, true);
            TwinizeSplit(m, NextOf(m, h));
            int h1 = TwinizeSplit(m, PrevOf(m, h));
            int g1 = None;
            int g = TwinOf(m, h);
            if (g != None)
            {
                SetActive(m, FaceOf(m, g), true);
                TwinizeSplit(m, PrevOf(m, g));
                g1 = TwinizeSplit(m, NextOf(m, g));
            }
            Loop(m, VtxOf(m, h), h1, g1);
        }

        // ------------------------------------------------------------------------------------------ test

        /// <summary>
        /// Two triangles sharing an edge (half-edges 0-2 and 3-5, with 0 and 3 twins): collapsing that edge
        /// deactivates the first triangle, and splitting it again brings it back.
        /// </summary>
        public static bool Demo()
        {
            Spec.Ensures((bool r) => r);
            var m = Own.New(new HMesh(
                next: new[] { 1, 2, 0, 4, 5, 3 }, prev: new[] { 2, 0, 1, 5, 3, 4 }, twin: new[] { 3, None, None, 0, None, None },
                vtx: new[] { 0, 1, 2, 1, 0, 3 }, face: new[] { 0, 0, 0, 1, 1, 1 }, active: new[] { true, true }, verts: 4), out var view);
            Own.ToAcc(view); // the region's permission, for the predicate
            Spec.Fold(Mesh(m));
            Collapse(m, 0);
            bool collapsed = !IsActive(m, 0);
            Split(m, 0);
            return collapsed && IsActive(m, 0);
        }
    }
}
