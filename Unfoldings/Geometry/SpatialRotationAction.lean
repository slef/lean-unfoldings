module

public import Unfoldings.Geometry.SpatialRotationMeasure
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! The action of the rotation matrices on spatial vectors. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialRotation

open Matrix MeasureTheory

/-- The spatial linear map represented by a rotation matrix. -/
def linear (g : SpatialRotation) : Space →ₗ[ℝ] Space := toEuclideanLin g.val

@[simp] theorem linear_one : linear 1 = LinearMap.id :=
  Matrix.toLpLin_one 2

@[simp] theorem linear_mul (g h : SpatialRotation) :
    linear (g * h) = (linear g).comp (linear h) :=
  Matrix.toLpLin_mul_same 2 _ _

theorem inner_linear (g : SpatialRotation) (x y : Space) :
    inner ℝ (linear g x) (linear g y) = inner ℝ x y := by
  have orthogonal := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp g.property).1
  have identity : (linear g).adjoint.comp (linear g) = LinearMap.id := by
    rw [linear, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change (toEuclideanLin g.valᵀ).comp (toEuclideanLin g.val) = LinearMap.id
    rw [← Matrix.toLpLin_mul_same 2, orthogonal, Matrix.toLpLin_one]
  rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply, identity, LinearMap.id_apply]

/-- Each spatial rotation is a linear isometry with inverse given by the inverse matrix. -/
def isometry (g : SpatialRotation) : Space ≃ₗᵢ[ℝ] Space where
  toFun := linear g
  invFun := linear g⁻¹
  left_inv x := by
    rw [← LinearMap.comp_apply, ← linear_mul, inv_mul_cancel, linear_one, LinearMap.id_apply]
  right_inv x := by
    rw [← LinearMap.comp_apply, ← linear_mul, mul_inv_cancel, linear_one, LinearMap.id_apply]
  map_add' := (linear g).map_add
  map_smul' := (linear g).map_smul
  norm_map' x := by
    change ‖linear g x‖ = ‖x‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [real_inner_self_eq_norm_sq] using inner_linear g x x

theorem continuous_apply :
    Continuous (fun z : SpatialRotation × Space => linear z.1 z.2) := by
  exact (PiLp.continuous_toLp 2 _).comp
    ((continuous_subtype_val.comp continuous_fst).matrix_mulVec
      ((PiLp.continuous_ofLp 2 _).comp continuous_snd))

/-- A positive-orientation linear isometry gives a rotation matrix in the
standard orthonormal spatial coordinates. -/
def ofIsometry (T : Space ≃ₗᵢ[ℝ] Space) (det_one : LinearMap.det T.toLinearMap = 1) :
    SpatialRotation := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  refine ⟨LinearMap.toMatrix b.toBasis b.toBasis T.toLinearMap, ?_⟩
  apply Matrix.mem_specialOrthogonalGroup_iff.mpr
  refine ⟨T.toMatrix_mem_unitaryGroup b b, ?_⟩
  rwa [LinearMap.det_toMatrix]

@[simp] theorem linear_ofIsometry (T : Space ≃ₗᵢ[ℝ] Space) (det_one) :
    linear (ofIsometry T det_one) = T.toLinearMap := by
  rw [linear, ofIsometry, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact LinearEquiv.apply_symm_apply _ _

open scoped InnerProductSpace in
/-- Rotations act transitively on every spatial sphere. Two orthogonal
reflections give the necessary positive orientation, including antipodal points. -/
theorem exists_linear_apply_eq_of_norm_eq {x y : Space} (norms : ‖x‖ = ‖y‖) :
    ∃ g : SpatialRotation, linear g x = y := by
  by_cases same : x = y
  · exact ⟨1, by simpa using same⟩
  have y_ne : y ≠ 0 := by
    intro zero
    rw [zero, norm_zero] at norms
    exact same ((norm_eq_zero.mp norms).trans zero.symm)
  let H := (ℝ ∙ y)ᗮ
  let : Fact (Module.finrank ℝ Space = 2 + 1) := ⟨by simp [Space]⟩
  have dimension : Module.finrank ℝ H = 2 :=
    Submodule.finrank_orthogonal_span_singleton y_ne
  let : Nontrivial H := Module.nontrivial_of_finrank_pos (by rw [dimension]; decide : 0 < _)
  obtain ⟨z, z_ne⟩ := exists_ne (0 : H)
  have z_ne' : (z : Space) ≠ 0 := fun zero => z_ne (Subtype.ext zero)
  let T := (ℝ ∙ (x - y))ᗮ.reflection
  let S := (ℝ ∙ (z : Space))ᗮ.reflection
  have first : T x = y := Submodule.reflection_sub norms
  have back : y ∈ (ℝ ∙ (z : Space))ᗮ := by
    have orthogonal : (z : Space) ∈ (ℝ ∙ y)ᗮ := z.property
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at orthogonal ⊢
    rwa [real_inner_comm]
  have last : S y = y := Submodule.reflection_mem_subspace_eq_self back
  have determinant {v : Space} (v_ne : v ≠ 0) :
      LinearMap.det ((ℝ ∙ v)ᗮ.reflection.toLinearMap) = -1 := by
    rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal,
      finrank_span_singleton v_ne, pow_one]
  let F := T.trans S
  have det_one : LinearMap.det F.toLinearMap = 1 := by
    change LinearMap.det (S.toLinearMap.comp T.toLinearMap) = 1
    rw [LinearMap.det_comp, determinant z_ne', determinant (sub_ne_zero.mpr same)]
    norm_num
  refine ⟨ofIsometry F det_one, ?_⟩
  rw [linear_ofIsometry]
  change S (T x) = y
  rw [first, last]

end Unfoldings.SpatialRotation
