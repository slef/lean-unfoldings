module

public import Unfoldings.Roof.CompatiblePotentialRadial
public import Unfoldings.Roof.CompatibleCutCarrier
public import Unfoldings.Convex.SegmentProgress

/-! Uniform estimates on whole paths and subpaths with arbitrary partial edges and terminal rays. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

def parentDirection (v : C.Vertex Set.univ) : Plane :=
  K.projectedVertex (R.parents.parent v) - K.projectedVertex v

theorem parent_local_progress (positive : 0 < a) (beta : 0 ≤ β) (acute : β ≤ Real.pi / 2)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes) {v : C.Vertex Set.univ}
    (nonroot : v ∉ R.parents.roots) :
    ∃ p, (G.boundaryEnvelope boundary).Active (K.projectedVertex v) p ∧
      (a * Real.cos β) * ‖R.parentDirection v‖ ≤ inner ℝ p (R.parentDirection v) := by
  have edge_ne : R.parentDirection v ≠ 0 := by
    intro zero
    have same := K.projectedVertex_injective (sub_eq_zero.mp zero)
    have strict := R.parents.ascending v nonroot
    rw [same] at strict
    exact lt_irrefl _ strict
  by_cases root : v ∈ R.original.parents.roots
  · let r : {v // v ∈ R.original.parents.roots} := ⟨v, root⟩
    have terminal : r ∉ R.exterior.parents.roots := fun h => nonroot ⟨root, h⟩
    have active := G.active_boundary boundary (R.exterior.active r)
      (R.exterior.slope_mem_frontier r)
    rw [R.exterior_points] at active
    refine ⟨R.exterior.slope r, active, ?_⟩
    have step := R.exterior.contact_inner_progress positive inner_disk
      (R.exterior.next_spec terminal).1
    simp only [R.exterior_points] at step
    have parent_eq := R.original.parents.attach_parent_root R.exterior.parents R.shared_height r
    change R.parents.parent v = (R.exterior.parents.parent r).val at parent_eq
    change (a * Real.cos β) * ‖K.projectedVertex (R.parents.parent v) - K.projectedVertex v‖ ≤
      inner ℝ (R.exterior.slope r)
        (K.projectedVertex (R.parents.parent v) - K.projectedVertex v)
    rw [parent_eq]
    have coefficient := mul_le_of_le_one_right positive.le (Real.cos_le_one β)
    exact (mul_le_mul_of_nonneg_right coefficient (norm_nonneg _)).trans step
  · obtain ⟨p, active, close, _progress, _endpoint⟩ := R.original.step v root
    refine ⟨p, active, ?_⟩
    have lower := G.boundary_norm_ge inner_disk active.1
    have angle : InnerProductGeometry.angle p (R.parentDirection v) ≤ β := by
      change InnerProductGeometry.angle p (_ - _) ≤ β
      rwa [R.original_parent root]
    exact SlopeEnvelope.direction_progress positive beta acute lower edge_ne angle

theorem terminal_local_progress (positive : 0 < a)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes) (r : {v // v ∈ R.parents.roots}) :
    ∃ p, (G.boundaryEnvelope boundary).Active (K.projectedVertex r.val) p ∧
      (a * Real.cos β) * ‖R.exterior.direction (R.exterior.slope (R.terminalIndex r))‖ ≤
        inner ℝ p (R.exterior.direction (R.exterior.slope (R.terminalIndex r))) := by
  let v := R.terminalIndex r
  have active := G.active_boundary boundary (R.exterior.active v)
    (R.exterior.slope_mem_frontier v)
  rw [R.exterior_points] at active
  refine ⟨R.exterior.slope v, active, ?_⟩
  rw [R.exterior.unit]
  have lower := R.exterior.rate_ge positive inner_disk v
  change a ≤ inner ℝ (R.exterior.direction (R.exterior.slope v)) (R.exterior.slope v) at lower
  have comm : inner ℝ (R.exterior.direction (R.exterior.slope v)) (R.exterior.slope v) =
      inner ℝ (R.exterior.slope v) (R.exterior.direction (R.exterior.slope v)) :=
    real_inner_comm _ _
  rw [comm] at lower
  nlinarith [mul_le_of_le_one_right positive.le (Real.cos_le_one β)]

/-- An oriented subsegment of a finite parent edge or a terminal straight ray. -/
def FollowsStep (x y : Plane) : Prop :=
  (∃ v : {v // v ∉ R.parents.roots}, ∃ s t : ℝ,
    0 ≤ s ∧ s ≤ t ∧ t ≤ 1 ∧
    x = K.projectedVertex v.val + s • R.parentDirection v.val ∧
    y = K.projectedVertex v.val + t • R.parentDirection v.val) ∨
  (∃ r : {v // v ∈ R.parents.roots}, ∃ s t : ℝ,
    0 ≤ s ∧ s ≤ t ∧ x = R.exterior.ray (R.terminalIndex r) s ∧
      y = R.exterior.ray (R.terminalIndex r) t)

def Follows {n : ℕ} (P : PolygonalChain Plane n) : Prop :=
  ∀ i : Fin n, R.FollowsStep (P.vertex i.castSucc) (P.vertex i.succ)

theorem followsStep_progress (positive : 0 < a) (beta : 0 ≤ β) (acute : β ≤ Real.pi / 2)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes) {x y : Plane}
    (step : R.FollowsStep x y) :
    (a * Real.cos β) * ‖y - x‖ ≤
      (G.boundaryEnvelope boundary).height y - (G.boundaryEnvelope boundary).height x := by
  rcases step with ⟨v, s, t, hs, ordered, _last, rfl, rfl⟩ |
    ⟨r, s, t, hs, ordered, rfl, rfl⟩
  · obtain ⟨p, active, gain⟩ := R.parent_local_progress positive beta acute inner_disk v.property
    exact (G.boundaryEnvelope boundary).ray_segment_progress active gain hs ordered
  · obtain ⟨p, active, gain⟩ := R.terminal_local_progress positive inner_disk r
    simp only [SlopeEnvelope.ExteriorPlan.ray, R.exterior_points]
    exact (G.boundaryEnvelope boundary).ray_segment_progress active gain hs ordered

/-- All partial edges and arbitrarily long terminal tails obey the same cumulative bound. -/
theorem follows_progress (positive : 0 < a) (beta : 0 ≤ β) (acute : β ≤ Real.pi / 2)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes) {n : ℕ} (P : PolygonalChain Plane n)
    (follows : R.Follows P) :
    (a * Real.cos β) * P.projectedLength ≤
      (G.boundaryEnvelope boundary).height (P.vertex (Fin.last n)) -
        (G.boundaryEnvelope boundary).height (P.vertex 0) :=
  P.potential_progress _
    (fun i => R.followsStep_progress positive beta acute inner_disk (follows i))

theorem follows_length_bound (positive : 0 < a) (beta : 0 ≤ β) (acute : β < Real.pi / 2)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes) {b : ℝ}
    (upper : ∀ p ∈ G.slopes, ‖p‖ ≤ b) {n : ℕ} (P : PolygonalChain Plane n)
    (follows : R.Follows P) :
    P.projectedLength ≤ (b / (a * Real.cos β)) * ‖P.vertex (Fin.last n) - P.vertex 0‖ :=
  (G.boundaryEnvelope boundary).history_length_bound
    (mul_pos positive (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], acute⟩))
    (fun p hp => upper p (G.compact.isClosed.frontier_subset hp))
    (R.follows_progress positive beta acute.le inner_disk P follows)

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
