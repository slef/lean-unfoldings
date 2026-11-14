module

public import Unfoldings.Roof.TruncatedCutGrowth
public import Unfoldings.Geometry.PrescribedSegments
public import Unfoldings.Convex.PhysicalModelMesh

/-! A small finite index for the bounded cut segments and their actual constraint equations. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)
  (level : ℝ) (higher : ∀ v, G.height (K.projectedVertex v) < level)

def cutFirst (i : Fin (Fintype.card (C.Vertex Set.univ))) : Plane :=
  R.truncatedPoint level (.inl ((Fintype.equivFin (C.Vertex Set.univ)).symm i))

def cutLast (i : Fin (Fintype.card (C.Vertex Set.univ))) : Plane :=
  R.truncatedPoint level ((R.truncatedParents level higher).parent
    (.inl ((Fintype.equivFin (C.Vertex Set.univ)).symm i)))

theorem truncatedCarrier_eq_segments :
    R.truncatedCarrier level higher = ⋃ i, segment ℝ (R.cutFirst level i)
      (R.cutLast level higher i) := by
  let e := Fintype.equivFin (C.Vertex Set.univ)
  ext x
  constructor
  · intro member
    obtain ⟨v, on_edge⟩ := Set.mem_iUnion.mp member
    exact Set.mem_iUnion.mpr ⟨e v, by
      change x ∈ segment ℝ (R.truncatedPoint level (.inl (e.symm (e v))))
        (R.truncatedPoint level ((R.truncatedParents level higher).parent (.inl (e.symm (e v)))))
      simpa only [e.symm_apply_apply] using on_edge⟩
  · intro member
    obtain ⟨i, on_edge⟩ := Set.mem_iUnion.mp member
    exact Set.mem_iUnion.mpr ⟨e.symm i, on_edge⟩

include higher in
theorem cutFirst_height (i : Fin (Fintype.card (C.Vertex Set.univ))) :
    G.height (R.cutFirst level i) < level := higher _

theorem cutLast_height (i : Fin (Fintype.card (C.Vertex Set.univ))) :
    G.height (R.cutLast level higher i) ≤ level := R.truncated_parent_height_le level higher _

/-- A nonempty original roof supplies a point strictly inside the chosen section. -/
def cutInteriorPoint : Plane :=
  let f := Classical.choice K.nonempty_face
  R.truncatedPoint 0 (.inl (C.vertexOfCorner Set.univ (f, 0)))

include higher in
theorem cutInteriorPoint_height : G.height R.cutInteriorPoint < level := higher _

end Unfoldings.ConvexRoof.CompatiblePotentialRouting

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)

include no_boundary in
theorem cut_endpoints_ne (i : Fin (Fintype.card (C.Vertex Set.univ))) :
    R.cutFirst level i ≠ R.cutLast level higher i := by
  let Q := K.truncatedCutEmbedding compact nonempty R no_boundary level higher
  let v := (Fintype.equivFin (C.Vertex Set.univ)).symm i
  let e : {v // v ∉ (R.truncatedParents level higher).roots} :=
    ⟨.inl v, R.parents.withLeaves_inl_nonroot level _ v⟩
  exact Q.vertex_injective.ne
    ((K.truncatedCutEmbedding_straight compact nonempty R no_boundary level higher).endpoints_ne e)

end Unfoldings.ConvexRoof
