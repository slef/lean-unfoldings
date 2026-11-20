module

public import Unfoldings.Geometry.SpatialPairFrame
public import Unfoldings.Geometry.EquatorPhase

/-! A proper spatial rotation places a given endpoint pair symmetrically on the equator. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialRotation

open InnerProductGeometry

private theorem det_linearIsometry_sq (L : Space ≃ₗᵢ[ℝ] Space) :
    LinearMap.det L.toLinearMap ^ 2 = 1 := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have unitary := L.toMatrix_mem_unitaryGroup b b
  have matrix := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp unitary
  have det := congrArg Matrix.det matrix
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, LinearMap.det_toMatrix] at det
  simpa only [pow_two] using det

private theorem pair_frame_to_rotation (u v : Space) (u_ne : u ≠ 0) (v_ne : v ≠ 0) :
    ∃ g : SpatialRotation,
      linear g u = ‖u‖ • complexLift 1 ∧
      linear g v = ‖v‖ • complexLift (polarRay (angle u v)) := by
  obtain ⟨L, h₁, h₂⟩ := exists_pair_frame u v u_ne v_ne
  have det := det_linearIsometry_sq L
  have signs : LinearMap.det L.toLinearMap = 1 ∨ LinearMap.det L.toLinearMap = -1 := by
    have zero : (LinearMap.det L.toLinearMap - 1) * (LinearMap.det L.toLinearMap + 1) = 0 := by
      linarith only [show (LinearMap.det L.toLinearMap - 1) *
        (LinearMap.det L.toLinearMap + 1) = LinearMap.det L.toLinearMap ^ 2 - 1 by ring, det]
    rcases mul_eq_zero.mp zero with pos | neg
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases signs with pos | neg
  · exact ⟨ofIsometry L pos, by rw [linear_ofIsometry]; exact h₁,
      by rw [linear_ofIsometry]; exact h₂⟩
  let reflection := (ℝ ∙ equatorPole)ᗮ.reflection
  have pole_ne : equatorPole ≠ 0 := norm_ne_zero_iff.mp (by rw [equatorPole_unit]; norm_num)
  have det_reflection : LinearMap.det reflection.toLinearMap = -1 := by
    dsimp only [reflection]
    rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal,
      finrank_span_singleton pole_ne, pow_one]
  have reflection_fixed (z : Space) (horizontal : z 2 = 0) : reflection z = z := by
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_equatorPole]
    exact horizontal
  have coordinate (r : ℝ) (w : ℂ) : (r • complexLift w) 2 = 0 := by
    rw [complexLift_apply]
    simp
  let T := L.trans reflection
  have det_T : LinearMap.det T.toLinearMap = 1 := by
    change LinearMap.det (reflection.toLinearMap.comp L.toLinearMap) = 1
    rw [LinearMap.det_comp, det_reflection, neg]
    norm_num
  refine ⟨ofIsometry T det_T, ?_, ?_⟩
  · rw [linear_ofIsometry]
    change reflection (L u) = _
    rw [h₁, reflection_fixed _ (coordinate _ _)]
  · rw [linear_ofIsometry]
    change reflection (L v) = _
    rw [h₂, reflection_fixed _ (coordinate _ _)]

theorem equatorPoint_coe_eq_complexLift (t : ℝ) :
    equatorPoint (t : EquatorPhase) = complexLift (polarRay t) := by
  rw [complexLift_apply]
  have eq : phaseComplex (t : EquatorPhase) = polarRay t := by
    simp [phaseComplex, AddCircle.toCircle, polarRay, Circle.exp,
      show (2 * Real.pi : ℝ) ≠ 0 by positivity]
  simp [equatorPoint, eq]

/-- Any two unit endpoints can be rotated to equatorial phases symmetric about
zero, with their angular separation giving the length of the arc. -/
theorem exists_centered_arc_rotation {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ g : SpatialRotation,
      linear g u = equatorPoint ((-(angle u v / 2) : ℝ) : EquatorPhase) ∧
      linear g v = equatorPoint ((angle u v / 2 : ℝ) : EquatorPhase) := by
  obtain ⟨g, left, right⟩ := pair_frame_to_rotation u v
    (norm_ne_zero_iff.mp (by rw [hu]; norm_num)) (norm_ne_zero_iff.mp (by rw [hv]; norm_num))
  let θ := angle u v
  have left' : linear g u = equatorPoint 0 := by
    rw [left, hu, one_smul, ← polarRay_zero]
    simpa only [AddCircle.coe_zero] using (equatorPoint_coe_eq_complexLift 0).symm
  have right' : linear g v = equatorPoint (θ : EquatorPhase) := by
    rw [right, hv, one_smul, equatorPoint_coe_eq_complexLift]
  let t : EquatorPhase := ((-(θ / 2) : ℝ) : EquatorPhase)
  refine ⟨phaseRotation t * g, ?_, ?_⟩
  · rw [linear_mul, LinearMap.comp_apply, left', linear_phaseRotation_equatorPoint, add_zero]
  · rw [linear_mul, LinearMap.comp_apply, right', linear_phaseRotation_equatorPoint]
    have eq : t + (θ : EquatorPhase) = ((θ / 2 : ℝ) : EquatorPhase) := by
      rw [← AddCircle.coe_add]
      congr 1
      ring
    rw [eq]

end Unfoldings.SpatialRotation
