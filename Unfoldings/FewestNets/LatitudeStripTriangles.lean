module

public import Unfoldings.FewestNets.LatitudeStripPartition
public import Mathlib.Analysis.Convex.Join

/-! When exactly one row advances, its sweep cell is the actual convex triangle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

private theorem horizontalSegment_iff {x y a : ℝ} (ordered : x ≤ y) {z : ℂ} :
    z ∈ segment ℝ (⟨x, a⟩ : ℂ) ⟨y, a⟩ ↔ z.im = a ∧ z.re ∈ Set.Icc x y := by
  constructor
  · rintro ⟨p, q, hp, hq, sum, rfl⟩
    simp only [Complex.real_smul, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero,
      Set.mem_Icc]
    have left := mul_le_mul_of_nonneg_left ordered hq
    have right := mul_le_mul_of_nonneg_left ordered hp
    have same₁ := congrArg (fun t : ℝ => t * a) sum
    have same₂ := congrArg (fun t : ℝ => t * x) sum
    have same₃ := congrArg (fun t : ℝ => t * y) sum
    exact ⟨by linarith only [same₁], by linarith only [left, same₂], by linarith only [right, same₃]⟩
  · rintro ⟨imag, low, high⟩
    rcases lt_or_eq_of_le ordered with different | equal
    · let p := (y - z.re) / (y - x)
      let q := (z.re - x) / (y - x)
      have positive : 0 < y - x := sub_pos.mpr different
      refine ⟨p, q, div_nonneg (sub_nonneg.mpr high) positive.le,
        div_nonneg (sub_nonneg.mpr low) positive.le, ?_, ?_⟩
      · dsimp only [p, q]
        rw [← add_div]
        convert div_self positive.ne' using 1
        ring
      · apply Complex.ext
        · simp only [Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, sub_zero, p, q]
          field_simp [positive.ne'] <;> ring
        · rw [imag]
          simp only [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, add_zero, p, q]
          field_simp [positive.ne'] <;> ring
    · subst y
      have value : z = (⟨x, a⟩ : ℂ) := Complex.ext (le_antisymm high low) imag
      exact value.symm ▸ left_mem_segment ℝ _ _

/-- At a given interpolation parameter, a triangle's horizontal slice is
the interval between the two interpolated sides. -/
theorem mem_parameter_triangle_iff {x y z₀ a b : ℝ} (ordered : x ≤ y) {z : ℂ} :
    z ∈ convexHull ℝ ({⟨z₀, b⟩, ⟨x, a⟩, ⟨y, a⟩} : Set ℂ) ↔
      ∃ t ∈ Set.Icc (0 : ℝ) 1, z.im = (1 - t) * a + t * b ∧
        z.re ∈ Set.Icc ((1 - t) * x + t * z₀) ((1 - t) * y + t * z₀) := by
  rw [convexHull_insert (Set.insert_nonempty _ _), convexHull_pair, mem_convexJoin]
  constructor
  · rintro ⟨apex, apex_eq, w, w_on, ha⟩
    rw [Set.mem_singleton_iff] at apex_eq
    subst apex
    obtain ⟨t, s, t_nonneg, s_nonneg, sum, rfl⟩ := ha
    obtain ⟨imag, low, high⟩ := (horizontalSegment_iff ordered).mp w_on
    have remain : s = 1 - t := by linarith only [sum]
    refine ⟨t, ⟨t_nonneg, by linarith only [sum, s_nonneg]⟩, ?_, ?_, ?_⟩
    · simp only [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, imag, remain]
      ring
    · simp only [Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      have bound := mul_le_mul_of_nonneg_left low s_nonneg
      rw [← remain]
      linarith only [bound]
    · simp only [Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      have bound := mul_le_mul_of_nonneg_left high s_nonneg
      rw [← remain]
      linarith only [bound]
  · rintro ⟨t, bounds, imag, location⟩
    by_cases at_apex : t = 1
    · subst t
      simp only [sub_self, zero_mul, zero_add, one_mul] at imag location
      have same : z = (⟨z₀, b⟩ : ℂ) := Complex.ext (le_antisymm location.2 location.1) imag
      refine ⟨⟨z₀, b⟩, Set.mem_singleton _, ⟨x, a⟩, left_mem_segment ℝ _ _, ?_⟩
      exact same.symm ▸ left_mem_segment ℝ _ _
    · have s_pos : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne bounds.2 at_apex)
      let u := (z.re - t * z₀) / (1 - t)
      have horizontal : u ∈ Set.Icc x y := by
        constructor
        · apply (le_div_iff₀ s_pos).mpr
          linarith only [location.1]
        · apply (div_le_iff₀ s_pos).mpr
          linarith only [location.2]
      refine ⟨⟨z₀, b⟩, Set.mem_singleton _, ⟨u, a⟩,
        (horizontalSegment_iff ordered).2 ⟨rfl, horizontal⟩,
        t, 1 - t, bounds.1, s_pos.le, by ring, ?_⟩
      apply Complex.ext
      · simp only [Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, u]
        field_simp [s_pos.ne'] <;> ring
      · simp only [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, add_zero, imag]
        ring

variable {n : ℕ} (lower upper : Fin (n + 1) → ℝ) (i : Fin n)

/-- Advancing a lower edge joins it to the current upper vertex. -/
theorem betweenCrossRows_eq_lower_triangle (ordered : lower i.castSucc ≤ lower i.succ)
    (upper_fixed : upper i.castSucc = upper i.succ) :
    betweenCrossRows lower upper i = convexHull ℝ
      ({⟨upper i.castSucc, 1⟩, ⟨lower i.castSucc, 0⟩, ⟨lower i.succ, 0⟩} : Set ℂ) := by
  ext z
  rw [mem_parameter_triangle_iff ordered]
  simp only [betweenCrossRows, crossRowLongitude, ← upper_fixed, mul_zero, mul_one, zero_add,
    Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨z.im, h.1, rfl, h.2⟩, fun ⟨_, ht, ht', range⟩ => ht'.symm ▸ ⟨ht, range⟩⟩

/-- Advancing an upper edge joins it to the current lower vertex. -/
theorem betweenCrossRows_eq_upper_triangle (ordered : upper i.castSucc ≤ upper i.succ)
    (lower_fixed : lower i.castSucc = lower i.succ) :
    betweenCrossRows lower upper i = convexHull ℝ
      ({⟨lower i.castSucc, 0⟩, ⟨upper i.castSucc, 1⟩, ⟨upper i.succ, 1⟩} : Set ℂ) := by
  ext z
  rw [mem_parameter_triangle_iff ordered]
  simp only [betweenCrossRows, crossRowLongitude, ← lower_fixed, mul_zero, mul_one, add_zero,
    Set.mem_ofPred_eq]
  constructor
  · intro member
    refine ⟨1 - z.im, ⟨sub_nonneg.mpr member.1.2, by linarith only [member.1.1]⟩, by ring, ?_⟩
    rw [sub_sub_cancel]
    exact ⟨by linarith only [member.2.1], by linarith only [member.2.2]⟩
  · rintro ⟨t, time, ht, range⟩
    rw [ht, sub_sub_cancel]
    exact ⟨⟨sub_nonneg.mpr time.2, by linarith only [time.1]⟩,
      ⟨by linarith only [range.1], by linarith only [range.2]⟩⟩

end Unfoldings.FewestNets
