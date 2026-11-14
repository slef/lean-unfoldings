module

public import Unfoldings.Roof.CompatibleCutPieces
public import Unfoldings.Topology.ParentLeaves
public import Unfoldings.Convex.EnvelopeSublevels

/-! Truncate terminal rays on a common level of the actual clipped envelope. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

theorem exists_truncation_level : ∃ level : ℝ, ∀ v, G.height (K.projectedVertex v) < level := by
  classical
  let h (v : C.Vertex Set.univ) := |G.height (K.projectedVertex v)|
  refine ⟨(∑ v, h v) + 1, fun v => ?_⟩
  have bound := Finset.single_le_sum (s := Finset.univ) (f := h)
    (fun w _ => abs_nonneg (G.height (K.projectedVertex w))) (Finset.mem_univ v)
  exact lt_of_le_of_lt ((le_abs_self _).trans bound) (lt_add_one _)

theorem parent_height_le (v : C.Vertex Set.univ) :
    R.parents.height v ≤ G.height (K.projectedVertex v) := by
  change R.original.parents.height v ≤ _
  rw [R.original.height_eq]
  exact G.boundary_height_le boundary _

theorem terminalIndex_terminal (r : {v // v ∈ R.parents.roots}) :
    R.terminalIndex r ∈ R.exterior.terminal := r.property.choose_spec

variable (level : ℝ) (higher : ∀ v, G.height (K.projectedVertex v) < level)

/-- The new finite forest has precisely the added boundary leaves as roots. -/
def truncatedParents : AscendingParents R.parents.LeafVertex :=
  R.parents.withLeaves level (fun v => (R.parent_height_le v).trans_lt (higher v))

/-- Actual positive travel time to the common height level along each terminal ray. -/
def terminalTime (r : {v // v ∈ R.parents.roots}) : ℝ :=
  (level - G.height (K.projectedVertex r.val)) / R.exterior.rate (R.terminalIndex r)

include higher in
theorem terminalTime_pos (r : {v // v ∈ R.parents.roots}) : 0 < R.terminalTime level r :=
  div_pos (sub_pos.mpr (higher r.val)) (R.exterior.positive _)

def terminalPoint (r : {v // v ∈ R.parents.roots}) : Plane :=
  R.exterior.ray (R.terminalIndex r) (R.terminalTime level r)

include higher in
theorem terminalPoint_level (r : {v // v ∈ R.parents.roots}) :
    G.height (R.terminalPoint level r) = level := by
  rw [terminalPoint, R.exterior.height_ray _ (R.terminalTime_pos level higher r).le,
    R.exterior_points]
  change G.height (K.projectedVertex r.val) +
    (level - G.height (K.projectedVertex r.val)) / R.exterior.rate (R.terminalIndex r) *
      R.exterior.rate (R.terminalIndex r) = level
  have nonzero : R.exterior.rate (R.terminalIndex r) ≠ 0 := ne_of_gt (R.exterior.positive _)
  rw [div_mul_cancel₀ _ nonzero]
  ring

include higher in
theorem terminalPoint_mem_openPiece (r : {v // v ∈ R.parents.roots}) :
    R.terminalPoint level r ∈ R.openPiece r.val := by
  rw [show R.openPiece r.val = R.exterior.openPiece (R.terminalIndex r) from
    R.openPiece_root (R.terminalIndex r),
    R.exterior.terminal_openPiece_eq (R.terminalIndex_terminal r)]
  exact ⟨R.terminalTime level r, R.terminalTime_pos level higher r, rfl⟩

theorem terminal_lineMap_eq_ray (r : {v // v ∈ R.parents.roots}) (t : ℝ) :
    AffineMap.lineMap (K.projectedVertex r.val) (R.terminalPoint level r) t =
      R.exterior.ray (R.terminalIndex r) (t * R.terminalTime level r) := by
  rw [terminalPoint, AffineMap.lineMap_apply_module']
  have first : R.exterior.point (R.terminalIndex r) = K.projectedVertex r.val :=
    R.exterior_points _
  dsimp [SlopeEnvelope.ExteriorPlan.ray]
  rw [first]
  module

include higher in
theorem terminal_segment_subset_openPiece (r : {v // v ∈ R.parents.roots}) :
    openSegment ℝ (K.projectedVertex r.val) (R.terminalPoint level r) ⊆ R.openPiece r.val := by
  rw [show R.openPiece r.val = R.exterior.openPiece (R.terminalIndex r) from
    R.openPiece_root (R.terminalIndex r),
    R.exterior.terminal_openPiece_eq (R.terminalIndex_terminal r), openSegment_eq_image_lineMap]
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨t * R.terminalTime level r, mul_pos ht.1 (R.terminalTime_pos level higher r),
    R.terminal_lineMap_eq_ray level r t⟩

/-- Old vertices keep their original coordinates; new leaves are actual ray endpoints. -/
def truncatedPoint : R.parents.LeafVertex → Plane
  | .inl v => K.projectedVertex v
  | .inr r => R.terminalPoint level r

include higher in
theorem truncatedPoint_level (r : {v // v ∈ R.parents.roots}) :
    G.height (R.truncatedPoint level (.inr r)) = level :=
  R.terminalPoint_level level higher r

theorem truncated_segment_subset_openPiece (v : C.Vertex Set.univ) :
    openSegment ℝ (R.truncatedPoint level (.inl v))
      (R.truncatedPoint level ((R.truncatedParents level higher).parent (.inl v))) ⊆
        R.openPiece v := by
  by_cases root : v ∈ R.parents.roots
  · change openSegment ℝ (K.projectedVertex v)
      (R.truncatedPoint level ((R.parents.withLeaves level _).parent (.inl v))) ⊆ _
    rw [R.parents.withLeaves_parent_root level _ ⟨v, root⟩]
    exact R.terminal_segment_subset_openPiece level higher ⟨v, root⟩
  · change openSegment ℝ (K.projectedVertex v)
      (R.truncatedPoint level ((R.parents.withLeaves level _).parent (.inl v))) ⊆ _
    rw [R.parents.withLeaves_parent_nonroot level _ root]
    exact R.parent_segment_subset_openPiece root

theorem truncated_parent_height_le (v : C.Vertex Set.univ) :
    G.height (R.truncatedPoint level ((R.truncatedParents level higher).parent (.inl v))) ≤
      level := by
  by_cases root : v ∈ R.parents.roots
  · change G.height (R.truncatedPoint level ((R.parents.withLeaves level _).parent (.inl v))) ≤ _
    rw [R.parents.withLeaves_parent_root level _ ⟨v, root⟩]
    exact (R.terminalPoint_level level higher ⟨v, root⟩).le
  · change G.height (R.truncatedPoint level ((R.parents.withLeaves level _).parent (.inl v))) ≤ _
    rw [R.parents.withLeaves_parent_nonroot level _ root]
    exact (higher _).le

theorem truncated_segment_height_lt (v : C.Vertex Set.univ) {x : Plane}
    (member : x ∈ openSegment ℝ (R.truncatedPoint level (.inl v))
      (R.truncatedPoint level ((R.truncatedParents level higher).parent (.inl v)))) :
    G.height x < level :=
  G.openSegment_height_lt (higher v) (R.truncated_parent_height_le level higher v) member

include higher in
theorem terminalPoint_mem_frontier (r : {v // v ∈ R.parents.roots}) :
    R.terminalPoint level r ∈ frontier {x | G.height x ≤ level} := by
  refine ⟨subset_closure (R.terminalPoint_level level higher r).le, ?_⟩
  intro inside
  obtain ⟨ε, positive, ball⟩ := Metric.isOpen_iff.mp isOpen_interior _ inside
  let t := R.terminalTime level r
  let y := R.exterior.ray (R.terminalIndex r) (t + ε / 2)
  have near : y ∈ Metric.ball (R.terminalPoint level r) ε := by
    apply Metric.mem_ball.mpr
    have difference : y - R.terminalPoint level r =
        (ε / 2) • R.exterior.direction (R.exterior.slope (R.terminalIndex r)) := by
      dsimp [y, t, terminalPoint, SlopeEnvelope.ExteriorPlan.ray]
      module
    rw [dist_eq_norm, difference, norm_smul, R.exterior.unit, Real.norm_eq_abs,
      abs_of_pos (by positivity), mul_one]
    linarith
  have below : G.height y ≤ level :=
    interior_subset (s := {x : Plane | G.height x ≤ level}) (ball near)
  have time : 0 < t := R.terminalTime_pos level higher r
  have base := R.exterior.height_ray (R.terminalIndex r) time.le
  have next := R.exterior.height_ray (R.terminalIndex r)
    (show 0 ≤ t + ε / 2 by positivity)
  have equal := R.terminalPoint_level level higher r
  change G.height (R.exterior.ray (R.terminalIndex r) t) = level at equal
  change G.height (R.exterior.ray (R.terminalIndex r) (t + ε / 2)) ≤ level at below
  rw [next] at below
  rw [base] at equal
  have rate : 0 < R.exterior.rate (R.terminalIndex r) := R.exterior.positive _
  nlinarith

theorem truncatedPoint_frontier_iff (v : R.parents.LeafVertex) :
    R.truncatedPoint level v ∈ frontier {x | G.height x ≤ level} ↔
      v ∈ (R.truncatedParents level higher).roots := by
  cases v with
  | inl v =>
    constructor
    · intro member
      exact (member.2 (G.mem_interior_sublevel (higher v))).elim
    · intro root
      exact ((R.parents.withLeaves_inl_nonroot level _ v) root).elim
  | inr r =>
    exact ⟨fun _ => ⟨r, rfl⟩, fun _ => R.terminalPoint_mem_frontier level higher r⟩

/-- Every original selected interior parent is preserved exactly after truncation. -/
theorem truncated_original_parent {v : C.Vertex Set.univ}
    (nonroot : v ∉ R.original.parents.roots) :
    (R.truncatedParents level higher).parent (.inl v) = .inl (R.original.parents.parent v) := by
  have final_nonroot : v ∉ R.parents.roots := fun root => nonroot root.choose
  change (R.parents.withLeaves level _).parent (.inl v) = _
  rw [R.parents.withLeaves_parent_nonroot level _ final_nonroot, R.original_parent nonroot]

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
