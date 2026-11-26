module

public import Unfoldings.FewestNets.RevisedLatitudeTrapezoid

/-! The exact number of midpoint-sweep triangles, with the two refined rows. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real
open scoped BigOperators

/-- Every advance in the midpoint sweep contributes one annular triangle. -/
def triangleCount (a : ℝ) : ℕ :=
  ∑ j ∈ Finset.range (stripCount a), (rowSize a j + rowSize a (j + 1))

private theorem sum_adjacent (f : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (f j + f (j + 1)) =
      f 0 + f (n + 1) + 2 * ∑ j ∈ Finset.range n, f (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

theorem triangleCount_lt_rows {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    (triangleCount a : ℝ) < 2 * (stripCount a : ℝ) + 1 + 1.903 / a +
      8 * π * (1 - 0.034 * a) / (spacing a * rowStep a) := by
  let N := stripCount a
  let b := spacing a
  let Δ := rowStep a
  let q := polarSampling a
  let w (j : ℕ) := 2 * π * sin (colatitude a j) / b
  have bp : 0 < b := spacing_pos positive
  have dp : 0 < Δ := rowStep_pos positive small
  have np : 0 < N := stripCount_pos positive small
  obtain ⟨n, hn_succ⟩ := Nat.exists_eq_succ_of_ne_zero np.ne'
  have hn : N = n + 1 := hn_succ
  have col_zero : colatitude a 0 = AcuteLatitudeGrid.polarRadius a := by simp [colatitude]
  have first : w 0 = q := by simp [w, q, b, polarSampling, col_zero]
  have last : w N = q := by
    dsimp only [w, N, q, polarSampling]
    rw [colatitude_last positive small, sin_pi_sub]
  have off_pole (j : ℕ) (hj : j ∈ Finset.range n) : (rowSize a (j + 1) : ℝ) ≤ w (j + 1) + 1 := by
    have below : j + 1 < N := by
      rw [hn]
      exact Nat.succ_lt_succ (Finset.mem_range.mp hj)
    have sine := sin_pos_of_mem_Ioo (colatitude_mem positive small below.le)
    have wn : 0 ≤ w (j + 1) := (div_pos (mul_pos (by positivity) sine) bp).le
    unfold rowSize
    rw [ite_eq_right (not_or.mpr ⟨Nat.succ_ne_zero _, below.ne⟩)]
    exact (Nat.ceil_lt_add_one wn).le
  have interior := Finset.sum_le_sum (fun j hj => off_pole j hj)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at interior
  have sizes :
      (triangleCount a : ℝ) < 2 * (N : ℝ) + 1 + (4 / 3 : ℝ) * q +
        ∑ j ∈ Finset.range N, (w j + w (j + 1)) := by
    unfold triangleCount
    push_cast
    change (∑ j ∈ Finset.range N, ((rowSize a j : ℝ) + (rowSize a (j + 1) : ℝ))) < _
    have last_size : rowSize a (n + 1) = polarSize a := by
      rw [← hn]
      exact rowSize_at_poles.2
    have last_weight : w (n + 1) = q := by rw [← hn, last]
    rw [hn, sum_adjacent, sum_adjacent, rowSize_at_poles.1, last_size, first, last_weight]
    have polar : (polarSize a : ℝ) < (5 / 3 : ℝ) * q + 1.5 :=
      polarSize_lt_sampling positive small
    push_cast
    linarith only [polar, interior]
  have polar_error : (4 / 3 : ℝ) * q < 1.903 / a := by
    apply (lt_div_iff₀ positive).mpr
    have upper : q * a < 1.42725 := (polarSampling_bounds positive small).2
    linarith only [show (4 / 3 : ℝ) * q * a = (4 / 3 : ℝ) * (q * a) by ring, upper]
  have bulk : (∑ j ∈ Finset.range N, (w j + w (j + 1))) ≤
      8 * π * (1 - 0.034 * a) / (b * Δ) := by
    calc
      _ = (4 * π / (b * Δ)) * (∑ j ∈ Finset.range N,
          (Δ / 2) * (sin (colatitude a j) + sin (colatitude a (j + 1)))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        dsimp only [w]
        field_simp [bp.ne', dp.ne']
        ring
      _ ≤ (4 * π / (b * Δ)) * (2 * (1 - 0.034 * a)) := by
        apply mul_le_mul_of_nonneg_left (weighted_sine_sum_bound positive small)
        positivity
      _ = _ := by ring
  exact sizes.trans_le (by linarith only [polar_error, bulk])

end Unfoldings.FewestNets.RevisedLatitudeGrid
