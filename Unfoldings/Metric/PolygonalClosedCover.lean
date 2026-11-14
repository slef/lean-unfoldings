module

public import Unfoldings.Metric.Polygonal
public import Unfoldings.Metric.FiniteCompleteCover
public import Mathlib.Topology.LocallyFinite

/-! Finite closed convex covers control intrinsic polygonal topology and completeness. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
  {I : Type*} [Finite I] (cells : I → Set E)
  (closed : ∀ i, IsClosed (cells i)) (convex : ∀ i, Convex ℝ (cells i))
  (cover : s = ⋃ i, cells i)

include cover in
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite I] in
private theorem cell_included (i : I) : cells i ⊆ s := by
  rw [cover]
  exact Set.subset_iUnion _ i

include closed convex cover in
/-- Closed finite polygonal regions have their actual subspace topology at every bank point. -/
theorem continuous_ofSubtype_of_finite_closed_cover : Continuous (ofSubtype (s := s)) := by
  let pieces (i : I) : Set s := {x | x.val ∈ cells i}
  have pieces_closed (i : I) : IsClosed (pieces i) :=
    (closed i).preimage continuous_subtype_val
  have pieces_cover : (⋃ i, pieces i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have member : x.val ∈ ⋃ i, cells i := cover ▸ x.property
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  apply (locallyFinite_of_finite pieces).continuous pieces_cover pieces_closed
  intro i
  apply continuousOn_iff_continuous_domRestrict.mpr
  let toCell : pieces i → cells i := fun x => ⟨x.val.val, x.property⟩
  have continuous_cell : Continuous toCell := by
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  exact (includeConvex_isometry (cells i) (convex i) (cell_included cells cover i)).continuous.comp
    continuous_cell

/-- This includes unbounded regions; the cells need not have a uniform diameter. -/
def closedCoverHomeomorph : PolygonalPoint s ≃ₜ s where
  toFun := toSubtype
  invFun := ofSubtype
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_toSubtype
  continuous_invFun := continuous_ofSubtype_of_finite_closed_cover cells closed convex cover

variable [CompleteSpace E]

include closed convex cover in
theorem completeSpace_of_finite_closed_cover : CompleteSpace (PolygonalPoint s) := by
  let complete (i : I) : CompleteSpace (cells i) := (closed i).isComplete.completeSpace_coe
  apply completeSpace_of_finite_isometric_cover (fun i => cells i)
    (fun i => includeConvex (cells i) (cell_included cells cover i))
    (fun i => includeConvex_isometry (cells i) (convex i) (cell_included cells cover i))
  intro x
  have member : x.val ∈ ⋃ i, cells i := cover ▸ x.property
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
  exact ⟨i, ⟨x.val, hi⟩, rfl⟩

end Unfoldings.PolygonalPoint
