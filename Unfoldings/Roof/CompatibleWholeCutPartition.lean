module

public import Unfoldings.Roof.CompatibleCutClosed
public import Unfoldings.Convex.FiniteSlopeModel
public import Unfoldings.Geometry.SpatialEnvelopeCut
public import Unfoldings.Geometry.SegmentEquation

/-! Construct actual unbounded roof partitions aligned to every compatible cut and terminal ray. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

open Classical in
/-- The original parent endpoint, or one unit step along the original terminal continuation. -/
def wholeCutLast (v : C.Vertex Set.univ) : Plane :=
  if root : v ∈ R.parents.roots then
    K.projectedVertex v + R.exterior.direction (R.exterior.slope (R.terminalIndex ⟨v, root⟩))
  else K.projectedVertex (R.parents.parent v)

/-- Proper supporting lines of the actual complete original cuts, with a small finite index type. -/
def wholeCutEquation (i : Fin (Fintype.card (C.Vertex Set.univ))) : Plane →ᵃ[ℝ] ℝ :=
  let v := (Fintype.equivFin (C.Vertex Set.univ)).symm i
  segmentEquation (K.projectedVertex v) (R.wholeCutLast v)

theorem wholeCutEquation_ne_zero (i : Fin (Fintype.card (C.Vertex Set.univ))) :
    R.wholeCutEquation i ≠ 0 := segmentEquation_ne_zero _ _

private theorem segmentEquation_lineMap (p q : Plane) (t : ℝ) :
    segmentEquation p q (AffineMap.lineMap p q t) = 0 := by
  rw [(segmentEquation p q).apply_lineMap,
    segmentEquation_eq_zero (left_mem_segment ℝ p q),
    segmentEquation_eq_zero (right_mem_segment ℝ p q)]
  simp only [AffineMap.lineMap_same, AffineMap.const_apply]

/-- Every point of every original finite cut or whole terminal ray has a named supporting line. -/
theorem carrier_covered_by_wholeCutEquations (x : Plane) (member : x ∈ R.carrier) :
    ∃ i, R.wholeCutEquation i x = 0 := by
  classical
  rcases member with finite | infinite
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp finite
    refine ⟨(Fintype.equivFin (C.Vertex Set.univ)) e.val, ?_⟩
    simp only [wholeCutEquation, Equiv.symm_apply_apply, wholeCutLast, dite_eq_right e.property]
    exact segmentEquation_eq_zero he
  · obtain ⟨r, t, nonnegative, equal⟩ := Set.mem_iUnion.mp infinite
    refine ⟨(Fintype.equivFin (C.Vertex Set.univ)) r.val, ?_⟩
    simp only [wholeCutEquation, Equiv.symm_apply_apply, wholeCutLast, dite_eq_left r.property]
    have source : R.exterior.point (R.terminalIndex r) = K.projectedVertex r.val :=
      R.exterior_points _
    rw [equal]
    change segmentEquation (K.projectedVertex r.val)
      (K.projectedVertex r.val + R.exterior.direction (R.exterior.slope (R.terminalIndex r)))
      (R.exterior.point (R.terminalIndex r) +
        t • R.exterior.direction (R.exterior.slope (R.terminalIndex r))) = 0
    rw [source]
    have expression : K.projectedVertex r.val +
        t • R.exterior.direction (R.exterior.slope (R.terminalIndex r)) =
        AffineMap.lineMap (K.projectedVertex r.val)
          (K.projectedVertex r.val +
            R.exterior.direction (R.exterior.slope (R.terminalIndex r))) t := by
      rw [AffineMap.lineMap_apply_module', add_sub_cancel_left, add_comm]
    rw [expression]
    exact segmentEquation_lineMap _ _ _

/-- The actual compatible one-ended cuts have a complete unbounded rigid planar-cell metric.
All cut supports and retained physical seams lie on actual cell boundaries. -/
theorem exists_whole_cut_partition (M : G.FiniteSlopeModel) :
    ∃ (A : Type) (_ : Fintype A) (P : SpatialEnvelope.WholePartition M.plane A),
      R.carrier ⊆ ⋃ a, frontier (P.footprint a) ∧ CompleteSpace (P.Cut R.carrier) ∧
      Function.Surjective (P.restoreCut R.carrier) := by
  obtain ⟨A, inst, P, signs, constrained⟩ := SpatialEnvelope.exists_wholePartition M.plane
    R.wholeCutEquation R.wholeCutEquation_ne_zero
  let : Fintype A := inst
  refine ⟨A, inst, P, ?_, P.cut_complete R.carrier, P.restoreCut_surjective R.carrier⟩
  intro x member
  obtain ⟨i, zero⟩ := R.carrier_covered_by_wholeCutEquations x member
  have covered : x ∈ ⋃ a, P.footprint a := P.cover.symm ▸ Set.mem_univ x
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp covered
  exact Set.mem_iUnion.mpr ⟨a, P.mem_frontier_of_constraint R.wholeCutEquation
    R.wholeCutEquation_ne_zero signs constrained a ha i zero⟩

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
