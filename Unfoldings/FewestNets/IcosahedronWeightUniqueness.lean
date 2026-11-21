module

public import Unfoldings.FewestNets.IcosahedronGridWeights
public import Unfoldings.FewestNets.IcosahedronFaceIntersections

/-! Barycentric weights on the original corners agree across the macroface boundaries. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Real
open scoped BigOperators

private theorem extendFaceWeights_of_supported (f : Fin 20) (w : Fin 12 → ℝ)
    (supported : ∀ i ∉ Set.range (faceVertex f), w i = 0) :
    extendFaceWeights f (w ∘ faceVertex f) = w := by
  funext i
  by_cases hi : i ∈ Set.range (faceVertex f)
  · obtain ⟨k, rfl⟩ := hi
    exact extendFaceWeights_faceVertex f _ k
  · rw [extendFaceWeights_zero_of_outside _ _ hi, supported i hi]

theorem face_weights_zero_of_outside (f : Fin 20) (w : Fin 12 → ℝ)
    (nonnegative : ∀ i, 0 ≤ w i) (total : ∑ i, w i = 1)
    (member : (∑ i, w i • rawVertex i) ∈ faceTriangle f) :
    ∀ i ∉ Set.range (faceVertex f), w i = 0 := by
  rw [faceTriangle_eq_support] at member
  let n := faceNormal f
  let h := 2 + 3 * goldenRatio
  have sum : ∑ i, w i * inner ℝ n (rawVertex i) = h := by
    have eq : inner ℝ n (∑ i, w i • rawVertex i) = h := member.2
    simpa only [inner_sum, real_inner_smul_right] using eq
  have zero : ∑ i, w i * (h - inner ℝ n (rawVertex i)) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, total, sum, one_mul, sub_self]
  have nonnegative' (i : Fin 12) : 0 ≤ w i * (h - inner ℝ n (rawVertex i)) :=
    mul_nonneg (nonnegative i) (sub_nonneg.mpr (inner_faceNormal_rawVertex_le f i))
  intro i hi
  have hzero :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => nonnegative' j)).mp zero i (Finset.mem_univ i)
  exact (mul_eq_zero.mp hzero).resolve_right
    (sub_ne_zero.mpr (inner_faceNormal_lt_of_outside f hi).ne.symm)

/-- If two convex combinations agree at a point of one macroface, their
twelve weights agree, including the zero weights off that face. -/
theorem eq_face_weights (f : Fin 20) (u v : Fin 12 → ℝ)
    (up : ∀ i, 0 ≤ u i) (vp : ∀ i, 0 ≤ v i)
    (us : ∑ i, u i = 1) (vs : ∑ i, v i = 1)
    (member : (∑ i, u i • rawVertex i) ∈ faceTriangle f)
    (same : ∑ i, u i • rawVertex i = ∑ i, v i • rawVertex i) :
    u = v := by
  have hu := extendFaceWeights_of_supported f u (face_weights_zero_of_outside f u up us member)
  have hv := extendFaceWeights_of_supported f v
    (face_weights_zero_of_outside f v vp vs (same ▸ member))
  suffices eq : u ∘ faceVertex f = v ∘ faceVertex f by
    rw [← hu, ← hv, eq]
  apply (linearIndependent_faceCorners f).fintypeLinearCombination_injective
  change (∑ d, (u ∘ faceVertex f) d • faceCorners f d) =
    ∑ d, (v ∘ faceVertex f) d • faceCorners f d
  rw [← sum_extendFaceWeights_smul, ← sum_extendFaceWeights_smul, hu, hv]
  exact same

end Unfoldings.FewestNets.Icosahedron
