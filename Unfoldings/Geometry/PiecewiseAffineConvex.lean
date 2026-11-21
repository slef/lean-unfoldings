module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Tactic

/-! Convexity of a piecewise-affine function from its actual neighboring slopes. -/

@[expose] public section

namespace Unfoldings

open Set

/-- A finite affine partition with common endpoint values and nondecreasing
slopes gives a convex function. Each affine piece supports the whole function. -/
theorem convexOn_of_monotone_affine_partition (n : ℕ) (time : ℕ → ℝ)
    (ordered : Monotone time) (slope intercept : ℕ → ℝ)
    (rising : ∀ i, i + 1 < n → slope i ≤ slope (i + 1))
    (joined : ∀ i, i + 1 < n →
      intercept i + slope i * time (i + 1) =
        intercept (i + 1) + slope (i + 1) * time (i + 1))
    {U : Set ℝ} (convex : Convex ℝ U) (f : ℝ → ℝ)
    (cover : ∀ x ∈ U, ∃ i < n, x ∈ Icc (time i) (time (i + 1)))
    (affine : ∀ i < n, ∀ x ∈ Icc (time i) (time (i + 1)),
      f x = intercept i + slope i * x) :
    ConvexOn ℝ U f := by
  let line (i : ℕ) (x : ℝ) := intercept i + slope i * x
  have step (i : ℕ) (in_range : i + 1 < n) (x : ℝ) :
      line (i + 1) x - line i x =
        (slope (i + 1) - slope i) * (x - time (i + 1)) := by
    dsimp [line]
    linarith only [joined i in_range]
  have forward (i j : ℕ) (ij : i ≤ j) (last : j < n) (x : ℝ) (after : time j ≤ x) :
      line i x ≤ line j x := by
    induction j, ij using Nat.le_induction with
    | base => exact le_rfl
    | succ k _ ih =>
      have previous := ih (by omega) ((ordered (Nat.le_succ k)).trans after)
      have nonneg := mul_nonneg (sub_nonneg.mpr (rising k last)) (sub_nonneg.mpr after)
      have diff := step k last x
      exact previous.trans (by linarith only [nonneg, diff])
  have backward (i j : ℕ) (ij : i ≤ j) (last : j < n) (x : ℝ)
      (before : x ≤ time (i + 1)) : line j x ≤ line i x := by
    induction j, ij using Nat.le_induction with
    | base => exact le_rfl
    | succ k ik ih =>
      have previous := ih (by omega)
      have nonpos := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (rising k last))
        (sub_nonpos.mpr (before.trans (ordered (Nat.succ_le_succ ik))))
      have diff := step k last x
      exact (show line (k + 1) x ≤ line k x by linarith only [nonpos, diff]).trans previous
  have supporting (i : ℕ) (hi : i < n) (x : ℝ) (hx : x ∈ U) : line i x ≤ f x := by
    obtain ⟨j, hj, hxj⟩ := cover x hx
    rw [affine j hj x hxj]
    rcases le_total i j with ij | ji
    · exact forward i j ij hj x hxj.1
    · exact backward j i ji hi x hxj.2
  refine ⟨convex, fun x hx y hy a b ha hb total => ?_⟩
  have inside := convex hx hy ha hb total
  obtain ⟨i, hi, on_piece⟩ := cover _ inside
  rw [affine i hi _ on_piece]
  have h := add_le_add (mul_le_mul_of_nonneg_left (supporting i hi x hx) ha)
    (mul_le_mul_of_nonneg_left (supporting i hi y hy) hb)
  change _ ≤ a * f x + b * f y
  apply le_trans _ h
  dsimp [line]
  linarith only [congrArg (intercept i * ·) total]

end Unfoldings
