module

public import Unfoldings.FewestNets.IcosahedronGridWeights
public import Unfoldings.Geometry.RadialConeCoordinates

/-! Every fine triangle has linearly independent corners before and after normalization. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open scoped BigOperators

private theorem sum_localGridWeights_mul {q : ℕ} (t : GridCell q) (c : Fin 3 → ℝ) (d : Fin 3) :
    ∑ k, c k * (localGridWeights t k d : ℝ) =
      (∑ k, c k) * (TriangleGrid.barycentricMin q t.val.1.val t.val.2.1.val t.val.2.2 d : ℝ) +
      (if t.val.2.2 then (∑ k, c k) - c d else c d) := by
  classical
  simp only [localGridWeights, TriangleGrid.barycentricCorner, Nat.cast_add, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  congr 1
  cases upper : t.val.2.2
  · simp [mul_ite]
  · simp only [Bool.true_eq_false, iff_false]
    have eq (k : Fin 3) : (if ¬d = k then (1 : ℝ) else 0) =
        1 - if k = d then (1 : ℝ) else 0 := by
      by_cases same : k = d
      · simp [same]
      · simp [same, Ne.symm same]
    simp_rw [eq, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
    simp

theorem linearIndependent_chordCorners {q : ℕ} (hq : 0 < q) (t : MeshFace q) :
    LinearIndependent ℝ (chordCorners t) := by
  rw [Fintype.linearIndependent_iff]
  intro c sum_zero
  have qne : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have expanded := sum_zero
  simp_rw [chordCorners_eq_localGridWeights hq, Finset.smul_sum, smul_smul,
    ← mul_div_assoc] at expanded
  rw [Finset.sum_comm] at expanded
  simp_rw [← Finset.sum_smul, ← Finset.sum_div] at expanded
  have each := Fintype.linearIndependent_iff.mp (linearIndependent_faceCorners t.1)
    (fun d => (∑ k, c k * (localGridWeights t.2 k d : ℝ)) / q) expanded
  have each_zero (d : Fin 3) : ∑ k, c k * (localGridWeights t.2 k d : ℝ) = 0 :=
    (div_eq_zero_iff.mp (each d)).resolve_right qne
  have total := Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin 3))) (fun d _ => each_zero d)
  rw [Finset.sum_comm] at total
  simp_rw [← Finset.mul_sum, ← Nat.cast_sum, sum_localGridWeights, ← Finset.sum_mul] at total
  have total_zero : ∑ k, c k = 0 := (mul_eq_zero.mp total).resolve_right qne
  intro d
  have hd := each_zero d
  rw [sum_localGridWeights_mul, total_zero, zero_mul, zero_add] at hd
  split at hd <;> linarith only [hd]

theorem linearIndependent_inscribedCorners {q : ℕ} (hq : 0 < q) (t : MeshFace q) :
    LinearIndependent ℝ (inscribedCorners t) := by
  let weight (i : Fin 3) := Units.mk0 ‖chordCorners t i‖ (norm_ne_zero_iff.mpr
    (chordCorners_ne_zero hq t i))
  exact (linearIndependent_chordCorners hq t).units_smul (fun i => (weight i)⁻¹)

end Unfoldings.FewestNets.Icosahedron
