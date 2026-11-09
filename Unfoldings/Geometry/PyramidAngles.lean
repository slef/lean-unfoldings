module

public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
public import Unfoldings.Geometry.AngleSeparation

/-!
# The lateral angle budget of a pyramid

Summing the angle sums of the lateral triangles and the angle triangle
inequality at the base vertices bounds the total apex angle. The successor
can be any permutation, so no polygon embedding or planar angle-sum theorem
is hidden in the hypotheses. Strictness at any base vertex makes the budget
strict as well.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

open EuclideanGeometry

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

theorem pyramid_angle_budget (next : Equiv.Perm ι) (apex : E) (base : ι → E)
    (different : ∀ i, base i ≠ apex) :
    (∑ i, angle (base i) apex (base (next i))) +
        (∑ i, angle (base (next.symm i)) (base i) (base (next i))) ≤
      (Fintype.card ι : ℝ) * Real.pi := by
  classical
  let A (i : ι) := angle (base i) apex (base (next i))
  let L (i : ι) := angle apex (base i) (base (next i))
  let R (i : ι) := angle (base i) (base (next i)) apex
  let B (i : ι) := angle (base (next.symm i)) (base i) (base (next i))
  have triangle (i : ι) : A i + L i + R i = Real.pi := by
    have sum := angle_add_angle_add_angle_eq_pi (base (next i)) (different i)
    dsimp only [A, L, R]
    linarith [angle_comm (base i) apex (base (next i))]
  have triangles : (∑ i, A i) + (∑ i, L i) + (∑ i, R i) =
      (Fintype.card ι : ℝ) * Real.pi := by
    have equal := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun i _ => triangle i)
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      using equal
  have bound (i : ι) : B i ≤ R (next.symm i) + L i := by
    simpa only [R, L, B, Equiv.apply_symm_apply] using
      angle_le_angle_add_angle (base i) (base (next.symm i)) apex (base (next i))
  have bases := Finset.sum_le_sum (s := Finset.univ) (fun i _ => bound i)
  rw [Finset.sum_add_distrib, next.symm.sum_comp R] at bases
  change (∑ i, A i) + (∑ i, B i) ≤ _
  linarith

theorem pyramid_angle_budget_strict (next : Equiv.Perm ι) (apex : E) (base : ι → E)
    (different : ∀ i, base i ≠ apex)
    (strict : ∃ i, angle (base (next.symm i)) (base i) (base (next i)) <
      angle (base (next.symm i)) (base i) apex + angle apex (base i) (base (next i))) :
    (∑ i, angle (base i) apex (base (next i))) +
        (∑ i, angle (base (next.symm i)) (base i) (base (next i))) <
      (Fintype.card ι : ℝ) * Real.pi := by
  classical
  let A (i : ι) := angle (base i) apex (base (next i))
  let L (i : ι) := angle apex (base i) (base (next i))
  let R (i : ι) := angle (base i) (base (next i)) apex
  let B (i : ι) := angle (base (next.symm i)) (base i) (base (next i))
  have triangle (i : ι) : A i + L i + R i = Real.pi := by
    have sum := angle_add_angle_add_angle_eq_pi (base (next i)) (different i)
    dsimp only [A, L, R]
    linarith [angle_comm (base i) apex (base (next i))]
  have triangles : (∑ i, A i) + (∑ i, L i) + (∑ i, R i) =
      (Fintype.card ι : ℝ) * Real.pi := by
    have equal := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun i _ => triangle i)
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      using equal
  have bound (i : ι) : B i ≤ R (next.symm i) + L i := by
    simpa only [R, L, B, Equiv.apply_symm_apply] using
      angle_le_angle_add_angle (base i) (base (next.symm i)) apex (base (next i))
  have one_strict : ∃ i ∈ Finset.univ, B i < R (next.symm i) + L i := by
    obtain ⟨i, hi⟩ := strict
    exact ⟨i, Finset.mem_univ _, by simpa only [R, L, B, Equiv.apply_symm_apply] using hi⟩
  have bases := Finset.sum_lt_sum (fun i _ => bound i) one_strict
  rw [Finset.sum_add_distrib, next.symm.sum_comp R] at bases
  change (∑ i, A i) + (∑ i, B i) < _
  linarith

/-- An apex outside the base level plane makes the budget strict at every
base vertex whose adjacent directions are not opposite. -/
theorem pyramid_angle_budget_strict_of_level (next : Equiv.Perm ι) (apex : E) (base : ι → E)
    (f : E →L[ℝ] ℝ) (h : ℝ) (nonzero : h ≠ 0)
    (level : ∀ i, f (base i - apex) = h)
    (corner : ∃ i, angle (base (next.symm i)) (base i) (base (next i)) ≠ Real.pi) :
    (∑ i, angle (base i) apex (base (next i))) +
        (∑ i, angle (base (next.symm i)) (base i) (base (next i))) <
      (Fintype.card ι : ℝ) * Real.pi := by
  have different (i : ι) : base i ≠ apex := by
    intro equal
    have height := level i
    rw [equal, sub_self, map_zero] at height
    exact nonzero height.symm
  apply pyramid_angle_budget_strict next apex base different
  obtain ⟨i, not_opposite⟩ := corner
  refine ⟨i, ?_⟩
  have difference (j k : ι) : f (base j - base k) = 0 := by
    have identity : base j - base k = (base j - apex) - (base k - apex) := by abel
    rw [identity, map_sub, level, level, sub_self]
  have transverse : f (apex - base i) ≠ 0 := by
    rw [← neg_sub, map_neg, level]
    exact neg_ne_zero.mpr nonzero
  exact angle_lt_angle_add_angle_of_transverse f (base (next.symm i) - base i)
    (apex - base i) (base (next i) - base i)
    (difference _ _) (difference _ _) transverse not_opposite

end Unfoldings
