module

public import Unfoldings.Roof.CompatiblePotentialRouting
public import Unfoldings.Convex.ExteriorProgress

/-! Whole-history estimates after interior forests and exterior continuations are attached. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

theorem parent_progress (positive : 0 < a)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes) (v : C.Vertex Set.univ) :
    (a * Real.cos β) * ‖K.projectedVertex (R.parents.parent v) - K.projectedVertex v‖ ≤
      (G.boundaryEnvelope boundary).height (K.projectedVertex (R.parents.parent v)) -
        (G.boundaryEnvelope boundary).height (K.projectedVertex v) := by
  by_cases original_root : v ∈ R.original.parents.roots
  · let r : {v // v ∈ R.original.parents.roots} := ⟨v, original_root⟩
    have parent_eq := R.original.parents.attach_parent_root R.exterior.parents R.shared_height r
    change R.parents.parent v = (R.exterior.parents.parent r).val at parent_eq
    rw [parent_eq]
    by_cases terminal : r ∈ R.exterior.parents.roots
    · rw [R.exterior.parents.fixed_root r terminal]
      change (a * Real.cos β) * ‖K.projectedVertex v - K.projectedVertex v‖ ≤
        (G.boundaryEnvelope boundary).height (K.projectedVertex v) -
          (G.boundaryEnvelope boundary).height (K.projectedVertex v)
      simp only [sub_self, norm_zero, mul_zero, le_refl]
    · have contact := (R.exterior.next_spec terminal).1
      have estimate := R.exterior.contact_boundary_progress positive inner_disk boundary contact
      simp only [R.exterior_points] at estimate
      have coefficient : a * Real.cos β ≤ a :=
        mul_le_of_le_one_right positive.le (Real.cos_le_one β)
      exact (mul_le_mul_of_nonneg_right coefficient (norm_nonneg _)).trans estimate
  · rw [R.original_parent original_root]
    obtain ⟨_p, _active, _close, progress, _endpoint⟩ := R.original.step v original_root
    exact progress

def history (start : C.Vertex Set.univ) (n : ℕ) : PolygonalChain Plane n :=
  ⟨fun i => K.projectedVertex (R.parents.parent^[i.val] start)⟩

theorem history_progress (positive : 0 < a)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes) (start : C.Vertex Set.univ) (n : ℕ) :
    (a * Real.cos β) * (R.history start n).projectedLength ≤
      (G.boundaryEnvelope boundary).height (K.projectedVertex (R.parents.parent^[n] start)) -
        (G.boundaryEnvelope boundary).height (K.projectedVertex start) := by
  apply (R.history start n).potential_progress (G.boundaryEnvelope boundary).height
  intro i
  simpa only [history, PolygonalChain.edge, Fin.val_succ, Fin.val_castSucc,
    Function.iterate_succ_apply'] using
    R.parent_progress positive inner_disk (R.parents.parent^[i.val] start)

/-- The uniform subpath length constant continues across all exterior mergers. Any starting
vertex and any number of parent steps are allowed. -/
theorem history_length_bound (positive : 0 < a) (beta : 0 ≤ β) (acute : β < Real.pi / 2)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes) {b : ℝ}
    (upper : ∀ p ∈ G.slopes, ‖p‖ ≤ b) (start : C.Vertex Set.univ) (n : ℕ) :
    (R.history start n).projectedLength ≤ (b / (a * Real.cos β)) *
      ‖K.projectedVertex (R.parents.parent^[n] start) - K.projectedVertex start‖ := by
  exact (G.boundaryEnvelope boundary).history_length_bound
    (mul_pos positive (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], acute⟩))
    (fun p hp => upper p (G.compact.isClosed.frontier_subset hp))
    (R.history_progress positive inner_disk start n)

/-- Every active boundary-potential slope at a merger controls all histories arriving there. -/
theorem history_angle_bound (positive : 0 < a) (beta : 0 ≤ β) (acute : β ≤ Real.pi / 2)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes) {b : ℝ} (bpos : 0 < b)
    (ratio : a * Real.cos β ≤ b) (upper : ∀ p ∈ G.slopes, ‖p‖ ≤ b)
    (start : C.Vertex Set.univ) (n : ℕ) {p : Plane}
    (active : (G.boundaryEnvelope boundary).Active
      (K.projectedVertex (R.parents.parent^[n] start)) p)
    (different : R.parents.parent^[n] start ≠ start) :
    InnerProductGeometry.angle p
      (K.projectedVertex (R.parents.parent^[n] start) - K.projectedVertex start) ≤
        Real.arccos ((a * Real.cos β) / b) := by
  have pne : p ≠ 0 := by
    intro zero
    have lower := G.boundary_norm_ge inner_disk active.1
    rw [zero, norm_zero] at lower
    linarith
  exact (G.boundaryEnvelope boundary).history_angle_bound bpos
    (mul_nonneg positive.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], acute⟩))
    ratio (fun p hp => upper p (G.compact.isClosed.frontier_subset hp)) active pne
    (K.projectedVertex_injective.ne different) (R.history_progress positive inner_disk start n)
    (R.history start n).chord_le_projectedLength

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
