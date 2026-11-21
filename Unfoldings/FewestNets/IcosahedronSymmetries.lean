module

public import Unfoldings.FewestNets.IcosahedronFaceIsometry
public import Unfoldings.FewestNets.IcosahedronFaceIntersections

/-! Finite dot products certify the symmetry taking one ordered face to another. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Real
open scoped BigOperators

private theorem exists_matching_vertex (f : Fin 20) (a b c : Fin 3)
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) (v : Fin 12) :
    ∃ w : Fin 12,
      dotData (faceVertex f a) w = dotData (faceVertex 0 0) v ∧
      dotData (faceVertex f b) w = dotData (faceVertex 0 1) v ∧
      dotData (faceVertex f c) w = dotData (faceVertex 0 2) v := by
  revert a b c ab ac bc v
  fin_cases f <;> decide +kernel

private theorem dotData_rawFaceGram (f : Fin 20) (i j : Fin 3) :
    inner ℝ (faceCorners f i) (faceCorners f j) =
      if i = j then 2 + goldenRatio else goldenRatio := by
  by_cases eq : i = j
  · subst j
    rw [ite_eq_left rfl]
    exact inner_rawVertex_self (faceVertex f i)
  · rw [ite_eq_right eq]
    exact inner_rawVertex_of_adjacent (adjacent_faceVertex f eq)

theorem eq_of_inner_faceCorners_eq (f : Fin 20) {x y : Space}
    (pairing : ∀ i, inner ℝ (faceCorners f i) x = inner ℝ (faceCorners f i) y) : x = y := by
  let B := basisOfLinearIndependentOfCardEqFinrank (linearIndependent_faceCorners f)
    (by simp [Space])
  have value (i : Fin 3) : B i = faceCorners f i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) i
  apply ext_inner_left ℝ
  intro z
  rw [← B.sum_repr z]
  simp only [sum_inner, real_inner_smul_left, value, pairing]

/-- Any ordering of any macroface is the image of the first ordered face under a
linear isometry preserving the full set of twelve icosahedral vertices. -/
theorem exists_isometry_ordered_macroface (f : Fin 20) (σ : Equiv.Perm (Fin 3)) :
    ∃ L : Space ≃ₗᵢ[ℝ] Space,
      (∀ j, L (faceCorners 0 j) = faceCorners f (σ j)) ∧
      (∀ v : Fin 12, ∃ w : Fin 12, L (rawVertex v) = rawVertex w) := by
  let A := basisOfLinearIndependentOfCardEqFinrank (linearIndependent_faceCorners 0)
    (by simp [Space])
  let B := basisOfLinearIndependentOfCardEqFinrank (linearIndependent_faceCorners f)
    (by simp [Space])
  have av (i : Fin 3) : A i = faceCorners 0 i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) i
  have bv (i : Fin 3) : B i = faceCorners f i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) i
  let E := A.equiv B σ
  have value (i : Fin 3) : E (faceCorners 0 i) = faceCorners f (σ i) := by
    rw [← av, ← bv, Module.Basis.equiv_apply]
  have sameInner (x y : Space) : inner ℝ (E x) (E y) = inner ℝ x y := by
    conv_lhs =>
      rw [← A.sum_repr x, ← A.sum_repr y]
    conv_rhs =>
      rw [← A.sum_repr x, ← A.sum_repr y]
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right, av, value, dotData_rawFaceGram, σ.injective.eq_iff]
  let L := E.isometryOfInner sameInner
  refine ⟨L, value, fun v => ?_⟩
  have ab : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have ac : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have bc : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  obtain ⟨w, h0, h1, h2⟩ := exists_matching_vertex f (σ 0) (σ 1) (σ 2) ab ac bc v
  refine ⟨w, eq_of_inner_faceCorners_eq f ?_⟩
  intro i
  obtain ⟨j, rfl⟩ := σ.surjective i
  have mapped : L (faceCorners 0 j) = faceCorners f (σ j) := value j
  calc
    inner ℝ (faceCorners f (σ j)) (L (rawVertex v)) =
        inner ℝ (faceCorners 0 j) (rawVertex v) := by rw [← mapped, L.inner_map_map]
    _ = inner ℝ (faceCorners f (σ j)) (rawVertex w) := ?_
  change inner ℝ (rawVertex (faceVertex 0 j)) (rawVertex v) =
    inner ℝ (rawVertex (faceVertex f (σ j))) (rawVertex w)
  rw [inner_rawVertex, inner_rawVertex]
  congr 1
  fin_cases j
  · exact h0.symm
  · exact h1.symm
  · exact h2.symm

end Unfoldings.FewestNets.Icosahedron
