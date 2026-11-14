module

public import Unfoldings.Roof.CommonPotentialForest
public import Unfoldings.Convex.PotentialPaths

/-! Uniform length and angle bounds for every actual incoming parent history. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CommonPotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {E : SlopeEnvelope} {a β : ℝ} (R : K.CommonPotentialRouting U E a β)

/-- Any finite parent history, including histories merging before the final root. -/
def history (start : C.Vertex Set.univ) (n : ℕ) : PolygonalChain Plane n :=
  ⟨fun i => K.projectedVertex (R.parents.parent^[i.val] start)⟩

theorem history_edge (start : C.Vertex Set.univ) (n : ℕ) (i : Fin n) :
    (R.history start n).edge i =
      K.projectedVertex (R.parents.parent (R.parents.parent^[i.val] start)) -
        K.projectedVertex (R.parents.parent^[i.val] start) := by
  simp only [history, PolygonalChain.edge, Fin.val_succ, Fin.val_castSucc,
    Function.iterate_succ_apply']

theorem parent_direction_ne_zero {v : C.Vertex Set.univ} (nonroot : v ∉ R.parents.roots) :
    K.projectedVertex (R.parents.parent v) - K.projectedVertex v ≠ 0 := by
  intro zero
  have same := K.projectedVertex_injective (sub_eq_zero.mp zero)
  have strict := R.parents.ascending v nonroot
  rw [same] at strict
  exact lt_irrefl _ strict

theorem history_choices (positive : 0 < a) (beta : 0 ≤ β) (acute : β ≤ Real.pi / 2)
    (lower : ∀ p ∈ E.slopes, a ≤ ‖p‖) (start : C.Vertex Set.univ) (n : ℕ) :
    ∀ i, ∃ p, E.Active ((R.history start n).vertex i.castSucc) p ∧
      (a * Real.cos β) * ‖(R.history start n).edge i‖ ≤
        inner ℝ p ((R.history start n).edge i) := by
  intro i
  let v := R.parents.parent^[i.val] start
  rw [R.history_edge]
  change ∃ p, E.Active (K.projectedVertex v) p ∧
    (a * Real.cos β) * ‖K.projectedVertex (R.parents.parent v) - K.projectedVertex v‖ ≤
      inner ℝ p (K.projectedVertex (R.parents.parent v) - K.projectedVertex v)
  by_cases root : v ∈ R.parents.roots
  · obtain ⟨p, active⟩ := E.exists_active (K.projectedVertex v)
    refine ⟨p, active, ?_⟩
    simp only [R.parents.fixed_root v root, sub_self, norm_zero, mul_zero, inner_zero_right,
      le_refl]
  · obtain ⟨p, active, close, _progress, _endpoint⟩ := R.step v root
    exact ⟨p, active, SlopeEnvelope.direction_progress positive beta acute
      (lower p active.1) (R.parent_direction_ne_zero root) close⟩

theorem history_length_bound (positive : 0 < a) (beta : 0 ≤ β) (acute : β < Real.pi / 2)
    (lower : ∀ p ∈ E.slopes, a ≤ ‖p‖) {b : ℝ} (upper : ∀ p ∈ E.slopes, ‖p‖ ≤ b)
    (start : C.Vertex Set.univ) (n : ℕ) :
    (R.history start n).projectedLength ≤ (b / (a * Real.cos β)) *
      ‖K.projectedVertex (R.parents.parent^[n] start) - K.projectedVertex start‖ := by
  exact E.path_length_bound (R.history start n)
    (mul_pos positive (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], acute⟩)) upper
    (R.history_choices positive beta acute.le lower start n)

/-- Any active slope at the merger controls every parent history arriving there. -/
theorem history_angle_bound (positive : 0 < a) (beta : 0 ≤ β) (acute : β ≤ Real.pi / 2)
    (lower : ∀ p ∈ E.slopes, a ≤ ‖p‖) {b : ℝ} (bpos : 0 < b)
    (ratio : a * Real.cos β ≤ b) (upper : ∀ p ∈ E.slopes, ‖p‖ ≤ b)
    (start : C.Vertex Set.univ) (n : ℕ) {p : Plane}
    (active : E.Active (K.projectedVertex (R.parents.parent^[n] start)) p)
    (different : R.parents.parent^[n] start ≠ start) :
    InnerProductGeometry.angle p
      (K.projectedVertex (R.parents.parent^[n] start) - K.projectedVertex start) ≤
        Real.arccos ((a * Real.cos β) / b) := by
  have pne : p ≠ 0 := by
    intro zero
    have bound := lower p active.1
    rw [zero, norm_zero] at bound
    linarith
  apply E.path_history_angle (R.history start n) bpos
    (mul_nonneg positive.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], acute⟩))
    ratio upper (R.history_choices positive beta acute lower start n) active pne
  exact K.projectedVertex_injective.ne different

end Unfoldings.ConvexRoof.CommonPotentialRouting
