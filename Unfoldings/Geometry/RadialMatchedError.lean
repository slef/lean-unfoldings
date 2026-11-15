module

public import Unfoldings.Geometry.RadialRayProgress

/-! Edgewise perturbations control actual matched bank points using quantitative radial progress. -/

@[expose] public section

open scoped NNReal

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P Q : PolygonalChain ℂ n) {γ ε : ℝ}
  (positive : 0 < γ) (small : γ ≤ 1) (error_nonnegative : 0 ≤ ε)
  (start : Q.vertex 0 = P.vertex 0)
  (margin : ∀ i, γ * (‖P.vertex i.castSucc - P.vertex 0‖ * ‖P.edge i‖) ≤
    inner ℝ (P.vertex i.castSucc - P.vertex 0) (P.edge i))
  (edge_error : ∀ i, ‖Q.edge i - P.edge i‖ ≤ ε * ‖P.edge i‖)

include positive small error_nonnegative start margin edge_error in
/-- The matched error is measured against the original vertex's true radius. -/
theorem radial_matched_vertex_error (v : Fin (n + 1)) :
    ‖Q.vertex v - P.vertex v‖ ≤ (ε / γ) * ‖P.vertex v - P.vertex 0‖ := by
  have coefficient : 0 ≤ ε / γ := div_nonneg error_nonnegative positive.le
  have cancel : (ε / γ) * γ = ε := div_mul_cancel₀ _ positive.ne'
  induction v using Fin.induction with
  | zero => simp [start]
  | succ v ih =>
    have progress := P.radial_edge_norm_progress (P.vertex 0) small margin v
    have scaled := mul_le_mul_of_nonneg_left progress coefficient
    rw [← mul_assoc, cancel, mul_sub] at scaled
    have equal : Q.vertex v.succ - P.vertex v.succ =
        (Q.vertex v.castSucc - P.vertex v.castSucc) + (Q.edge v - P.edge v) := by
      simp only [edge]
      abel
    rw [equal]
    have triangle := norm_add_le (Q.vertex v.castSucc - P.vertex v.castSucc) (Q.edge v - P.edge v)
    nlinarith [edge_error v]

include positive small error_nonnegative start margin edge_error in
/-- The same constant controls each true partial edge, without adding endpoint vertices. -/
theorem radial_matched_point_error (i : Fin n) (t : unitInterval) :
    ‖Q.point i t - P.point i t‖ ≤ (ε / γ) * ‖P.point i t - P.vertex 0‖ := by
  have coefficient : 0 ≤ ε / γ := div_nonneg error_nonnegative positive.le
  have cancel : (ε / γ) * γ = ε := div_mul_cancel₀ _ positive.ne'
  have vertex_bound := P.radial_matched_vertex_error Q positive small error_nonnegative
    start margin edge_error i.castSucc
  have progress := P.radial_point_norm_progress (P.vertex 0) positive.le small margin
    i 0 t t.property.1
  have length : ‖P.point i t - P.vertex i.castSucc‖ = (t : ℝ) * ‖P.edge i‖ := by
    simp only [point, AffineMap.lineMap_apply_module', add_sub_cancel_right, edge, norm_smul,
      Real.norm_of_nonneg t.property.1]
  rw [P.point_zero, length] at progress
  have scaled := mul_le_mul_of_nonneg_left progress coefficient
  rw [← mul_assoc, cancel, mul_sub] at scaled
  have equal : Q.point i t - P.point i t =
      (Q.vertex i.castSucc - P.vertex i.castSucc) + (t : ℝ) • (Q.edge i - P.edge i) := by
    simp only [point, edge, AffineMap.lineMap_apply_module']
    module
  have triangle := norm_add_le (Q.vertex i.castSucc - P.vertex i.castSucc)
    ((t : ℝ) • (Q.edge i - P.edge i))
  rw [norm_smul, Real.norm_of_nonneg t.property.1] at triangle
  rw [equal]
  nlinarith [mul_le_mul_of_nonneg_left (edge_error i) t.property.1]

end Unfoldings.PolygonalChain

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R Q : PolygonalRay ℂ n) {γ ε : ℝ}
  (positive : 0 < γ) (small : γ ≤ 1) (error_nonnegative : 0 ≤ ε) (start : Q.start = R.start)
  (margin : ∀ i, γ * (‖R.chain.vertex i.castSucc - R.start‖ * ‖R.chain.edge i‖) ≤
    inner ℝ (R.chain.vertex i.castSucc - R.start) (R.chain.edge i))
  (tail_margin : γ * (‖R.chain.vertex (Fin.last n) - R.start‖ * ‖R.direction‖) ≤
    inner ℝ (R.chain.vertex (Fin.last n) - R.start) R.direction)
  (edge_error : ∀ i, ‖Q.chain.edge i - R.chain.edge i‖ ≤ ε * ‖R.chain.edge i‖)
  (tail_error : ‖Q.direction - R.direction‖ ≤ ε * ‖R.direction‖)

include positive small error_nonnegative start margin tail_margin edge_error tail_error in
/-- Hinge translations are retained at the start of the true infinite tail. -/
theorem radial_matched_tail_error (t : ℝ≥0) :
    ‖Q.tail t - R.tail t‖ ≤ (ε / γ) * ‖R.tail t - R.start‖ := by
  have vertex_bound := R.chain.radial_matched_vertex_error Q.chain positive small error_nonnegative
    start margin edge_error (Fin.last n)
  change ‖Q.chain.vertex (Fin.last n) - R.chain.vertex (Fin.last n)‖ ≤
    (ε / γ) * ‖R.chain.vertex (Fin.last n) - R.start‖ at vertex_bound
  have progress := R.radial_tail_norm_progress positive.le small tail_margin 0 t zero_le
  have length : ‖R.tail t - R.tail 0‖ = (t : ℝ) * ‖R.direction‖ := by
    rw [R.tail_zero, tail, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg t.coe_nonneg]
  rw [length, R.tail_zero] at progress
  have coefficient : 0 ≤ ε / γ := div_nonneg error_nonnegative positive.le
  have cancel : (ε / γ) * γ = ε := div_mul_cancel₀ _ positive.ne'
  have scaled := mul_le_mul_of_nonneg_left progress coefficient
  rw [← mul_assoc, cancel, mul_sub] at scaled
  have equal : Q.tail t - R.tail t =
      (Q.chain.vertex (Fin.last n) - R.chain.vertex (Fin.last n)) +
        (t : ℝ) • (Q.direction - R.direction) := by
    simp only [tail]
    module
  have triangle := norm_add_le (Q.chain.vertex (Fin.last n) - R.chain.vertex (Fin.last n))
    ((t : ℝ) • (Q.direction - R.direction))
  rw [norm_smul, Real.norm_of_nonneg t.coe_nonneg] at triangle
  rw [equal]
  nlinarith [mul_le_mul_of_nonneg_left tail_error t.coe_nonneg]

include positive small error_nonnegative start margin tail_margin edge_error tail_error in
/-- Every point of the actual perturbed bank has an actual matched original bank point. -/
theorem exists_radial_matched_point {z : ℂ} (member : z ∈ Q.carrier) :
    ∃ x ∈ R.carrier, ‖z - x‖ ≤ (ε / γ) * ‖x - R.start‖ := by
  rcases member with finite_member | ⟨t, rfl⟩
  · have cover := Q.chain.path_range.subset finite_member
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at cover
    rcases cover with initial | ⟨i, t, rfl⟩
    · refine ⟨R.start, R.start_mem, ?_⟩
      rw [Set.mem_singleton_iff.mp initial]
      change ‖Q.start - R.start‖ ≤ (ε / γ) * ‖R.start - R.start‖
      simp only [start, sub_self, norm_zero, mul_zero, le_refl]
    · exact ⟨R.chain.point i t, Or.inl (R.chain.point_mem_path_range i t),
        R.chain.radial_matched_point_error Q.chain positive small error_nonnegative
          start margin edge_error i t⟩
  · exact ⟨R.tail t, R.tail_mem t,
      R.radial_matched_tail_error Q positive small error_nonnegative start margin tail_margin
        edge_error tail_error t⟩

end Unfoldings.PolygonalRay
