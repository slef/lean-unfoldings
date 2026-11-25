module

public import Unfoldings.Geometry.MinorArcArclength

/-! A rotation exchanging the ends of a geodesic side and reversing its normal. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialRotation

open scoped InnerProductSpace

/-- A half-turn about the midpoint axis preserves a side as a set and
interchanges the two halfspaces bounded by its supporting plane. -/
theorem exists_side_flip {a b n : Space} (different : a ≠ b) (norms : ‖a‖ = ‖b‖)
    (normal_ne : n ≠ 0) (ha : inner ℝ n a = 0) (hb : inner ℝ n b = 0) :
    ∃ g : SpatialRotation, linear g a = b ∧ linear g b = a ∧ linear g n = -n ∧
      linear g '' closedMinorArc a b = closedMinorArc a b := by
  let T := (ℝ ∙ (a - b))ᗮ.reflection
  let S := (ℝ ∙ n)ᗮ.reflection
  have Ta : T a = b := Submodule.reflection_sub norms
  have Tb : T b = a := by
    have swap := (ℝ ∙ (a - b))ᗮ.reflection_reflection a
    change T (T a) = a at swap
    rwa [Ta] at swap
  have Tn : T n = n := by
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right, ha, hb, sub_zero]
  have Sa : S a = a := by
    apply Submodule.reflection_mem_subspace_eq_self
    rwa [Submodule.mem_orthogonal_singleton_iff_inner_left, real_inner_comm]
  have Sb : S b = b := by
    apply Submodule.reflection_mem_subspace_eq_self
    rwa [Submodule.mem_orthogonal_singleton_iff_inner_left, real_inner_comm]
  have Sn : S n = -n := Submodule.reflection_orthogonalComplement_singleton_eq_neg n
  have determinant {z : Space} (ne : z ≠ 0) :
      LinearMap.det ((ℝ ∙ z)ᗮ.reflection.toLinearMap) = -1 := by
    rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal, finrank_span_singleton ne, pow_one]
  let F := T.trans S
  have det_one : LinearMap.det F.toLinearMap = 1 := by
    change LinearMap.det (S.toLinearMap.comp T.toLinearMap) = 1
    rw [LinearMap.det_comp, determinant normal_ne, determinant (sub_ne_zero.mpr different)]
    norm_num
  let g := ofIsometry F det_one
  have ga : linear g a = b := by
    change linear (ofIsometry F det_one) a = b
    rw [linear_ofIsometry]
    change S (T a) = b
    rw [Ta, Sb]
  have gb : linear g b = a := by
    change linear (ofIsometry F det_one) b = a
    rw [linear_ofIsometry]
    change S (T b) = a
    rw [Tb, Sa]
  refine ⟨g, ga, gb, ?_, ?_⟩
  · change linear (ofIsometry F det_one) n = -n
    rw [linear_ofIsometry]
    change S (T n) = -n
    rw [Tn, Sn]
  · rw [image_closedMinorArc, ga, gb]
    exact closedMinorArc_comm b a

end Unfoldings.SpatialRotation
