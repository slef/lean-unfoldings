module

public import Unfoldings.Roof.CompatibleCutPieces
public import Unfoldings.Roof.CompatibleTerminalBanks
public import Unfoldings.Metric.PlanarRayCutBanks

/-! Exact finite closed pieces of the actual compatible forest, including complete terminal rays. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

open Classical in
/-- The entire finite parent edge or complete final ray belonging to an original vertex. -/
def closedPiece (v : C.Vertex Set.univ) : Set Plane :=
  if root : v ∈ R.parents.roots then
    {x | ∃ t : ℝ, 0 ≤ t ∧ x = R.exterior.ray (R.terminalIndex ⟨v, root⟩) t}
  else segment ℝ (K.projectedVertex v) (K.projectedVertex (R.parents.parent v))

theorem carrier_eq_iUnion_closedPiece : R.carrier = ⋃ v, R.closedPiece v := by
  classical
  ext x
  constructor
  · rintro (finite | infinite)
    · obtain ⟨v, member⟩ := Set.mem_iUnion.mp finite
      exact Set.mem_iUnion.mpr ⟨v.val, by simpa only [closedPiece, dite_eq_right v.property]⟩
    · obtain ⟨v, member⟩ := Set.mem_iUnion.mp infinite
      exact Set.mem_iUnion.mpr ⟨v.val, by simpa only [closedPiece, dite_eq_left v.property]⟩
  · intro member
    obtain ⟨v, member⟩ := Set.mem_iUnion.mp member
    by_cases root : v ∈ R.parents.roots
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨v, root⟩, by
        simpa only [closedPiece, dite_eq_left root] using member⟩)
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨v, root⟩, by
        simpa only [closedPiece, dite_eq_right root] using member⟩)

theorem closedPiece_root (r : {v // v ∈ R.parents.roots}) :
    R.closedPiece r.val = MetricGluing.rayCut (K.projectedVertex r.val) (R.wholeCutLast r.val) := by
  classical
  simp only [closedPiece, dite_eq_left r.property]
  ext x
  constructor
  · rintro ⟨t, ht, equal⟩
    exact ⟨⟨t, ht⟩, (R.terminal_lineMap r t).trans equal.symm⟩
  · rintro ⟨t, equal⟩
    exact ⟨t, t.coe_nonneg, equal.symm.trans (R.terminal_lineMap r t)⟩

theorem isClosed_closedPiece (v : C.Vertex Set.univ) : IsClosed (R.closedPiece v) := by
  classical
  by_cases root : v ∈ R.parents.roots
  · rw [R.closedPiece_root ⟨v, root⟩]
    exact MetricGluing.isClosed_rayCut _ _
  · simpa only [closedPiece, dite_eq_right root] using
      (compact_segment (K.projectedVertex v)
        (K.projectedVertex (R.parents.parent v))).isClosed

/-- Apart from original vertex endpoints, the entire closed piece lies in its actual open piece. -/
theorem closedPiece_mem_open_or_vertex (v : C.Vertex Set.univ) {x : Plane}
    (member : x ∈ R.closedPiece v) : x ∈ R.openPiece v ∨ ∃ w, x = K.projectedVertex w := by
  classical
  by_cases root : v ∈ R.parents.roots
  · simp only [closedPiece, dite_eq_left root] at member
    obtain ⟨t, ht, equal⟩ := member
    rcases ht.eq_or_lt with rfl | positive
    · right
      refine ⟨v, ?_⟩
      rw [SlopeEnvelope.ExteriorPlan.ray, zero_smul, add_zero, R.exterior_points] at equal
      exact equal
    · left
      rw [R.openPiece_root ⟨v, root.choose⟩, R.exterior.terminal_openPiece_eq root.choose_spec]
      exact ⟨t, positive, equal⟩
  · simp only [closedPiece, dite_eq_right root] at member
    rw [← insert_endpoints_openSegment] at member
    rcases member with first | last | on_open
    · exact Or.inr ⟨v, first⟩
    · exact Or.inr ⟨R.parents.parent v, last⟩
    · exact Or.inl (R.parent_segment_subset_openPiece root on_open)

/-- A positive terminal point belongs to its actual open piece. -/
theorem terminal_ray_mem_openPiece (r : {v // v ∈ R.parents.roots}) {t : ℝ} (positive : 0 < t) :
    R.exterior.ray (R.terminalIndex r) t ∈ R.openPiece r.val := by
  rw [R.openPiece_root ⟨r.val, r.property.choose⟩,
    R.exterior.terminal_openPiece_eq r.property.choose_spec]
  exact ⟨t, positive, rfl⟩

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
