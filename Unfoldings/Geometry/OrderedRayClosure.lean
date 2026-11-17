module

public import Unfoldings.Geometry.SupportedVertexAvoidingClosure
public import Unfoldings.Geometry.AxisQuadrantFrame

/-! Strictly ordered original ray subdivisions construct their radial closure geometry. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane (n + 1)) (origin direction : Plane)
  (nonzero : direction ≠ 0) (time : Fin (n + 2) → ℝ) (nonnegative : ∀ i, 0 ≤ time i)
  (increasing : StrictMono time)
  (position : ∀ i, P.vertex i = origin + time i • direction)

include nonzero nonnegative increasing position in
/-- Every genuine ordered ray subdivision admits strict radial progress and a pointed
supporting wedge from any source a positive distance behind its original ray origin. -/
theorem ordered_ray_closure_geometry {d : ℝ} (behind : 0 < d) :
    let source := origin - d • direction
    source ∈ P.strictRadialSources ∧ 0 < dist source (P.vertex 0) ∧
      dist source (P.vertex 0) < dist source (P.vertex (Fin.last (n + 1))) ∧
      ∃ frame : (ℝ × ℝ) ≃ₗ[ℝ] Plane, ∀ j,
        0 ≤ (frame.symm (P.vertex j - source)).1 ∧
          0 ≤ (frame.symm (P.vertex j - source)).2 := by
  let source := origin - d • direction
  have difference (j : Fin (n + 2)) :
      P.vertex j - source = (time j + d) • direction := by
    rw [position]
    dsimp only [source]
    module
  have edges (i : Fin (n + 1)) :
      P.edge i = (time i.succ - time i.castSucc) • direction := by
    rw [edge, position, position]
    module
  have positive (j : Fin (n + 2)) : 0 < time j + d :=
    add_pos_of_nonneg_of_pos (nonnegative j) behind
  have norm_positive : 0 < ‖direction‖ := norm_pos_iff.mpr nonzero
  have distance (j : Fin (n + 2)) :
      dist source (P.vertex j) = (time j + d) * ‖direction‖ := by
    rw [dist_eq_norm', difference, norm_smul, Real.norm_of_nonneg (positive j).le]
  have strict : source ∈ P.strictRadialSources := by
    intro i _
    rw [difference, edges, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    exact mul_pos (positive i.castSucc)
      (mul_pos (sub_pos.mpr (increasing Fin.castSucc_lt_succ)) (sq_pos_of_pos norm_positive))
  have initial : 0 < dist source (P.vertex 0) := by
    rw [distance]
    exact mul_pos (positive 0) norm_positive
  have progress : dist source (P.vertex 0) < dist source (P.vertex (Fin.last (n + 1))) := by
    rw [distance, distance]
    apply mul_lt_mul_of_pos_right _ norm_positive
    have ordered := increasing (show (0 : Fin (n + 2)) < Fin.last (n + 1) from by
      change 0 < n + 1
      omega)
    linarith
  let frame := axisQuadrantFrame direction
  have axis : 0 < (frame.symm direction).1 ∧ 0 < (frame.symm direction).2 :=
    axisQuadrantFrame_positive nonzero (by
      rw [InnerProductGeometry.angle_self nonzero]
      positivity)
  refine ⟨strict, initial, progress, frame, fun j => ?_⟩
  rw [difference, map_smul]
  exact ⟨mul_nonneg (positive j).le axis.1.le, mul_nonneg (positive j).le axis.2.le⟩

end Unfoldings.PolygonalChain
