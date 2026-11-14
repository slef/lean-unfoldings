module

public import Unfoldings.Roof.CompatiblePotentialPaths
public import Unfoldings.Convex.AnnularHistoryMargin
public import Unfoldings.Geometry.RadialMarginSegment

/-! Radial margins on whole compatible paths, including partial edges and terminal tails. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

open Classical in
/-- Every vertex has an actual forward direction, including the straight tail at a final root. -/
def outgoingDirection (v : C.Vertex Set.univ) : Plane :=
  if root : v ∈ R.parents.roots then
    R.exterior.direction (R.exterior.slope (R.terminalIndex ⟨v, root⟩)) else R.parentDirection v

theorem outgoingDirection_ne_zero (v : C.Vertex Set.univ) : R.outgoingDirection v ≠ 0 := by
  classical
  by_cases root : v ∈ R.parents.roots
  · rw [outgoingDirection, dite_eq_left root]
    intro zero
    have unit := R.exterior.unit (R.terminalIndex ⟨v, root⟩)
    rw [zero, norm_zero] at unit
    norm_num at unit
  · rw [outgoingDirection, dite_eq_right root]
    intro zero
    have same := K.projectedVertex_injective (sub_eq_zero.mp zero)
    have strict := R.parents.ascending v root
    rw [same] at strict
    exact lt_irrefl _ strict

theorem outgoing_active_angle (positive : 0 < a) {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes)
    (upper : ∀ p ∈ G.slopes, ‖p‖ ≤ b) (v : C.Vertex Set.univ) :
    ∃ p, (G.boundaryEnvelope boundary).Active (K.projectedVertex v) p ∧
      (InnerProductGeometry.angle p (R.outgoingDirection v) ≤ β ∨
        InnerProductGeometry.angle p (R.outgoingDirection v) ≤ Real.arccos (a / b)) := by
  classical
  by_cases root : v ∈ R.parents.roots
  · let r := R.terminalIndex ⟨v, root⟩
    have active := G.active_boundary boundary (R.exterior.active r)
      (R.exterior.slope_mem_frontier r)
    rw [R.exterior_points] at active
    refine ⟨R.exterior.slope r, active, Or.inr ?_⟩
    rw [outgoingDirection, dite_eq_left root]
    exact R.exterior.direction_angle_bound positive bpos ratio inner_disk upper r
  · rw [outgoingDirection, dite_eq_right root]
    exact R.parent_active_angle positive bpos ratio inner_disk upper root

/-- Every incoming compatible path, with arbitrary partial first and last edges, has the
same positive margin against the next actual outgoing edge or terminal ray. -/
theorem follows_radial_margin (positive : 0 < a) (beta : 0 ≤ β) (acute : β < Real.pi / 2)
    {b ζ : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes)
    (upper : ∀ p ∈ G.slopes, ‖p‖ ≤ b)
    (sector : Real.tan β < a / b) (zeta : 0 ≤ ζ) (direction : Real.arccos (a / b) ≤ ζ)
    (exterior : annularHistoryAngle (a / b) β + ζ < Real.pi / 2)
    {n : ℕ} (P : PolygonalChain Plane n) (follows : R.Follows P) (v : C.Vertex Set.univ)
    (last : P.vertex (Fin.last n) = K.projectedVertex v)
    (different : P.vertex (Fin.last n) ≠ P.vertex 0) :
    annularRadialMargin (a / b) β ζ *
      (‖P.vertex (Fin.last n) - P.vertex 0‖ * ‖R.outgoingDirection v‖) ≤
        inner ℝ (P.vertex (Fin.last n) - P.vertex 0) (R.outgoingDirection v) := by
  obtain ⟨p, active, close⟩ := R.outgoing_active_angle positive bpos ratio inner_disk upper v
  have pne : p ≠ 0 := by
    intro zero
    have lower := G.boundary_norm_ge inner_disk active.1
    rw [zero, norm_zero] at lower
    linarith
  have active_last : (G.boundaryEnvelope boundary).Active (P.vertex (Fin.last n)) p :=
    last.symm ▸ active
  exact (G.boundaryEnvelope boundary).annular_history_radial_margin positive bpos ratio beta acute
    (fun p hp => upper p (G.compact.isClosed.frontier_subset hp)) sector zeta exterior active_last
    pne different (R.outgoingDirection_ne_zero v)
    (R.follows_progress positive beta acute.le inner_disk P follows) P.chord_le_projectedLength
    (close.elim Or.inl (fun bound => Or.inr (bound.trans direction)))

/-- Radial control holds throughout each subsequent straight piece, not only at its
initial vertex. For terminal roots, time is unrestricted. -/
theorem follows_radial_margin_along_outgoing
    (positive : 0 < a) (beta : 0 ≤ β) (acute : β < Real.pi / 2)
    {b ζ : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes)
    (upper : ∀ p ∈ G.slopes, ‖p‖ ≤ b)
    (sector : Real.tan β < a / b) (zeta : 0 ≤ ζ) (direction : Real.arccos (a / b) ≤ ζ)
    (exterior : annularHistoryAngle (a / b) β + ζ < Real.pi / 2)
    {n : ℕ} (P : PolygonalChain Plane n) (follows : R.Follows P) (v : C.Vertex Set.univ)
    (last : P.vertex (Fin.last n) = K.projectedVertex v)
    (different : P.vertex (Fin.last n) ≠ P.vertex 0) {t : ℝ} (time : 0 ≤ t) :
    annularRadialMargin (a / b) β ζ *
      (‖(P.vertex (Fin.last n) + t • R.outgoingDirection v) - P.vertex 0‖ *
        ‖R.outgoingDirection v‖) ≤
      inner ℝ ((P.vertex (Fin.last n) + t • R.outgoingDirection v) - P.vertex 0)
        (R.outgoingDirection v) := by
  have margin := R.follows_radial_margin positive beta acute bpos ratio inner_disk upper
    sector zeta direction exterior P follows v last different
  have good := annular_radial_margin_pos (div_pos positive bpos)
    ((div_le_one bpos).mpr ratio) beta acute sector zeta exterior
  have small : annularRadialMargin (a / b) β ζ ≤ 1 :=
    (min_le_left _ _).trans (Real.cos_le_one _)
  have expression : (P.vertex (Fin.last n) + t • R.outgoingDirection v) - P.vertex 0 =
      (P.vertex (Fin.last n) - P.vertex 0) + t • R.outgoingDirection v := by abel
  rw [expression]
  exact radial_margin_along_ray good.le small time margin

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
