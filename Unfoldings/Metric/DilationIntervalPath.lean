module

public import Unfoldings.Metric.PositiveClosedInterval
public import Mathlib.Topology.MetricSpace.Dilation
public import Mathlib.Topology.Path

/-! Traverse the exact original closed time interval of an entire metric half-line dilation. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings

variable {X : Type*} [EMetricSpace X] (f : ℝ≥0 →ᵈ X) (s t : ℝ≥0) (ordered : s ≤ t)

/-- Follow a dilation from its original initial time to its original final time. -/
def dilationIntervalPath : Path (f s) (f t) where
  toFun u := f (nonnegativeIntervalLineMap s.val t.val s.property ordered u)
  continuous_toFun := (Dilation.lipschitzWith f).continuous.comp
    (continuous_nonnegativeIntervalLineMap s.val t.val s.property ordered)
  source' := by
    congr 1
    apply Subtype.ext
    simp only [nonnegativeIntervalLineMap, Set.Icc.coe_zero, zero_mul, add_zero]
  target' := by
    congr 1
    apply Subtype.ext
    simp only [nonnegativeIntervalLineMap, Set.Icc.coe_one, one_mul, add_sub_cancel]

/-- No actual ray time is omitted or added, including both original endpoint copies. -/
theorem dilationIntervalPath_range : Set.range (dilationIntervalPath f s t ordered) =
    f '' Set.Icc s t := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨_, ⟨?_, ?_⟩, rfl⟩
    · change s.val ≤ s.val + u.val * (t.val - s.val)
      exact le_add_of_nonneg_right (mul_nonneg u.property.1 (sub_nonneg.mpr ordered))
    · change s.val + u.val * (t.val - s.val) ≤ t.val
      nlinarith [mul_le_mul_of_nonneg_right u.property.2 (sub_nonneg.mpr ordered)]
  · rintro ⟨a, bounds, rfl⟩
    by_cases same : s = t
    · have at_s : a = s := le_antisymm (same ▸ bounds.2) bounds.1
      exact ⟨0, by simpa only [at_s] using (dilationIntervalPath f s t ordered).source⟩
    have positive : 0 < t.val - s.val := sub_pos.mpr
      (lt_of_le_of_ne (show s.val ≤ t.val from ordered) (fun eq => same (Subtype.ext eq)))
    have last_bound : a.val ≤ t.val := bounds.2
    let u : unitInterval := ⟨(a.val - s.val) / (t.val - s.val),
      div_nonneg (sub_nonneg.mpr bounds.1) positive.le,
      (div_le_one positive).mpr (by change a.val - s.val ≤ t.val - s.val; linarith [last_bound])⟩
    refine ⟨u, congrArg f (Subtype.ext ?_)⟩
    change s.val + ((a.val - s.val) / (t.val - s.val)) * (t.val - s.val) = a.val
    rw [div_mul_cancel₀ _ positive.ne']
    ring

/-- Append the actual terminal interval of a dilation to a path with the same intrinsic
endpoint. Only that original endpoint equality is used to join the paths. -/
def appendDilationPath {a b : X} (P : Path a b) (same : b = f s) : Path a (f t) :=
  P.trans ((dilationIntervalPath f s t ordered).cast same rfl)

/-- The joined path has precisely its original stem and original closed terminal interval. -/
theorem appendDilationPath_range {a b : X} (P : Path a b) (same : b = f s) :
    Set.range (appendDilationPath f s t ordered P same) = Set.range P ∪ f '' Set.Icc s t := by
  rw [appendDilationPath, Path.trans_range]
  change Set.range P ∪ Set.range (dilationIntervalPath f s t ordered) = _
  rw [dilationIntervalPath_range]

include ordered in
/-- If the positive terminal tail avoids the original stem, the closed pieces meet
exactly at their actual common intrinsic endpoint, including a zero-length tail. -/
theorem path_inter_dilation_interval {a b : X} (P : Path a b) (same : b = f s)
    (separated : ∀ u : ℝ≥0, s < u → f u ∉ Set.range P) :
    Set.range P ∩ f '' Set.Icc s t = {f s} := by
  apply Set.Subset.antisymm
  · rintro x ⟨on_path, u, bounds, at_x⟩
    have at_start : u = s := by
      apply le_antisymm ?_ bounds.1
      by_contra after
      exact separated u (lt_of_not_ge after) (at_x ▸ on_path)
    exact Set.mem_singleton_iff.mpr (at_x.symm.trans (congrArg f at_start))
  · intro x member
    rw [Set.mem_singleton_iff.mp member]
    exact ⟨⟨1, P.target.trans same⟩, s, ⟨le_rfl, ordered⟩, rfl⟩

end Unfoldings
