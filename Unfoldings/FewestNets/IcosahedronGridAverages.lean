module

public import Unfoldings.FewestNets.IcosahedronGridBoxes
public import Unfoldings.FewestNets.IcosahedronWeightUniqueness

/-! Relate a convex average of small triangles' integer weights to its point in space. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open scoped BigOperators

def gridAverage {q : ℕ} (t : MeshFace q) (w : Fin 3 → ℝ) (i : Fin 12) : ℝ :=
  ∑ k, w k * (gridWeights t k i : ℝ)

theorem sum_gridAverage {q : ℕ} (t : MeshFace q) (w : Fin 3 → ℝ) (total : ∑ k, w k = 1) :
    ∑ i, gridAverage t w i = (q : ℝ) := by
  simp only [gridAverage]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← Nat.cast_sum, sum_gridWeights, ← Finset.sum_mul, total, one_mul]

theorem gridAverage_bounds {q : ℕ} (t : MeshFace q) (w : Fin 3 → ℝ)
    (nonnegative : ∀ k, 0 ≤ w k) (total : ∑ k, w k = 1) (i : Fin 12) :
    (gridMin t i : ℝ) ≤ gridAverage t w i ∧ gridAverage t w i ≤ (gridMax t i : ℝ) := by
  have low (k : Fin 3) : (gridMin t i : ℝ) ≤ gridWeights t k i := by
    exact_mod_cast (gridWeights_bounds t k i).1
  have high (k : Fin 3) : (gridWeights t k i : ℝ) ≤ gridMax t i := by
    exact_mod_cast (gridWeights_bounds t k i).2
  constructor
  · have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3))) (fun k _ =>
      mul_le_mul_of_nonneg_left (low k) (nonnegative k))
    rw [← Finset.sum_mul, total, one_mul] at h
    exact h
  · have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3))) (fun k _ =>
      mul_le_mul_of_nonneg_left (high k) (nonnegative k))
    rw [← Finset.sum_mul, total, one_mul] at h
    exact h

theorem sum_gridAverage_smul {q : ℕ} (hq : 0 < q) (t : MeshFace q) (w : Fin 3 → ℝ) :
    ∑ k, w k • chordCorners t k = ∑ i, (gridAverage t w i / q) • rawVertex i := by
  simp_rw [chordCorners_eq_gridWeights hq, Finset.smul_sum, smul_smul, ← mul_div_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, ← Finset.sum_div, gridAverage]

/-- Different triangle labels for the same point of the mesh give the same
average of the global integer coordinates. -/
theorem gridAverage_eq_of_same_point {q : ℕ} (hq : 0 < q) (t s : MeshFace q) (u v : Fin 3 → ℝ)
    (up : ∀ k, 0 ≤ u k) (vp : ∀ k, 0 ≤ v k) (us : ∑ k, u k = 1) (vs : ∑ k, v k = 1)
    (same : ∑ k, u k • chordCorners t k = ∑ k, v k • chordCorners s k) :
    gridAverage t u = gridAverage s v := by
  have qpos : (0 : ℝ) < q := by exact_mod_cast hq
  have member : (∑ k, u k • chordCorners t k) ∈ faceTriangle t.1 :=
    chordTriangle_subset_faceTriangle hq t (mem_convexHull_of_exists_fintype u (chordCorners t)
      up us (fun k => Set.mem_range_self k) rfl)
  rw [sum_gridAverage_smul hq t] at member same
  rw [sum_gridAverage_smul hq s] at same
  have nonnegative (r : MeshFace q) (w : Fin 3 → ℝ) (hw : ∀ k, 0 ≤ w k) (i : Fin 12) :
      0 ≤ gridAverage r w i / q :=
    div_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (by positivity)) qpos.le
  have total (r : MeshFace q) (w : Fin 3 → ℝ) (hw : ∑ k, w k = 1) :
      ∑ i, gridAverage r w i / q = 1 := by
    rw [← Finset.sum_div, sum_gridAverage r w hw, div_self qpos.ne']
  have eq := eq_face_weights t.1 _ _ (nonnegative t u up) (nonnegative s v vp)
    (total t u us) (total s v vs) member same
  funext i
  exact (div_left_inj' qpos.ne').mp (congrFun eq i)

end Unfoldings.FewestNets.Icosahedron
