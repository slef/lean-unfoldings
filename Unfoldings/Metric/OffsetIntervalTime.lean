module

public import Unfoldings.Metric.HalfOpenIntervalExtension
public import Mathlib.Basic.NNReal.Basic

/-! Relative interval parameters retain exact original ray time after a fixed offset. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

/-- Original ray time on a half-open interval beginning at a named nonnegative time. -/
def offsetNonnegativeIcoParameter (start : ℝ≥0) {T : ℝ} (t : Set.Ico (0 : ℝ) T) : ℝ≥0 :=
  start + nonnegativeIcoParameter t

/-- Original ray time on the closed interval, retaining both endpoint parameters. -/
def offsetNonnegativeIccParameter (start : ℝ≥0) {T : ℝ} (t : Set.Icc (0 : ℝ) T) : ℝ≥0 :=
  start + ⟨t.val, t.property.1⟩

theorem offsetNonnegativeIcoParameter_isometry (start : ℝ≥0) {T : ℝ} :
    Isometry (offsetNonnegativeIcoParameter start (T := T)) := by
  intro s t
  change edist ((start : ℝ) + s.val) ((start : ℝ) + t.val) = edist s.val t.val
  simp only [edist_dist, Real.dist_eq]
  congr 2
  ring

theorem offsetNonnegativeIccParameter_isometry (start : ℝ≥0) {T : ℝ} :
    Isometry (offsetNonnegativeIccParameter start (T := T)) := by
  intro s t
  change edist ((start : ℝ) + s.val) ((start : ℝ) + t.val) = edist s.val t.val
  simp only [edist_dist, Real.dist_eq]
  congr 2
  ring

end Unfoldings
