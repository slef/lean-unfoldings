module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Order.Filter.Finite

/-! An upper slope bound survives finite changes of the active differentiable branch. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Filter Set
open scoped Topology

/-- One-sided bounds on secants at every point give the global upper slope
bound. In particular, no differentiability is required at changes of branch. -/
theorem sub_le_mul_of_eventually_right_slope {f : ℝ → ℝ} {a b K : ℝ}
    (ab : a ≤ b) (continuous : ContinuousOn f (Icc a b))
    (local_bound : ∀ x ∈ Ico a b, ∀ L > K, ∀ᶠ y in 𝓝[Ioc x b] x, slope f x y < L) :
    f b - f a ≤ K * (b - a) := by
  by_cases equal : a = b
  · simp [equal]
  have lt : a < b := lt_of_le_of_ne ab equal
  by_contra fail
  let L := (K + (f b - f a) / (b - a)) / 2
  have better : K < (f b - f a) / (b - a) :=
    (lt_div_iff₀ (sub_pos.mpr lt)).mpr (lt_of_not_ge fail)
  have KL : K < L := by dsimp [L]; linarith
  have Ls : L < (f b - f a) / (b - a) := by dsimp [L]; linarith
  let g (x : ℝ) := f x - L * x
  have g_cont : ContinuousOn g (Icc a b) := continuous.sub
    (continuousOn_const.mul continuousOn_id)
  have gap : g a < g b := by
    have h := (lt_div_iff₀ (sub_pos.mpr lt)).mp Ls
    dsimp [g]
    linarith only [h]
  obtain ⟨x, hx, min⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr ab) g_cont
  have xb : x < b := by
    apply lt_of_le_of_ne hx.2
    intro same
    exact gap.not_ge (same ▸ (isMinOn_iff.mp min a ⟨le_rfl, ab⟩))
  have xcl : x ∈ closure (Ioc x b) := by
    rw [closure_Ioc xb.ne]
    exact ⟨le_rfl, xb.le⟩
  let : NeBot (𝓝[Ioc x b] x) := mem_closure_iff_nhdsWithin_neBot.mp xcl
  have eventual : ∀ᶠ y in 𝓝[Ioc x b] x, y ∈ Ioc x b ∧ slope f x y < L :=
    (show ∀ᶠ y in 𝓝[Ioc x b] x, y ∈ Ioc x b from self_mem_nhdsWithin).and
      (local_bound x ⟨hx.1, xb⟩ L KL)
  obtain ⟨y, hy, s⟩ := eventual.exists
  have h := (div_lt_iff₀ (sub_pos.mpr hy.1)).mp (by simpa only [slope_def_field] using s)
  have down : g y < g x := by dsimp [g]; linarith only [h]
  exact down.not_ge (isMinOn_iff.mp min y ⟨hx.1.trans hy.1.le, hy.2⟩)

/-- A continuous function which selects from finitely many continuous branches
inherits the common upper bound on the active branch derivatives. -/
theorem sub_le_mul_of_finite_selection {I : Type*} [Finite I]
    {f : ℝ → ℝ} {a b K : ℝ} (ab : a ≤ b) (continuous : ContinuousOn f (Icc a b))
    (branch : I → ℝ → ℝ) (branch_cont : ∀ i, ContinuousOn (branch i) (Icc a b))
    (chooses : ∀ x ∈ Icc a b, ∃ i, f x = branch i x)
    (rates : ∀ x ∈ Ico a b, ∀ i, f x = branch i x →
      ∃ d ≤ K, HasDerivAt (branch i) d x) :
    f b - f a ≤ K * (b - a) := by
  apply sub_le_mul_of_eventually_right_slope ab continuous
  intro x hx L KL
  have x_in : x ∈ Icc a b := ⟨hx.1, hx.2.le⟩
  have subset : Ioc x b ⊆ Icc a b := fun y hy => ⟨hx.1.trans hy.1.le, hy.2⟩
  have all (i : I) : ∀ᶠ y in 𝓝[Ioc x b] x, f y = branch i y → slope f x y < L := by
    by_cases active : f x = branch i x
    · obtain ⟨d, d_le, deriv⟩ := rates x hx i active
      have within : 𝓝[Ioc x b] x ≤ 𝓝[≠] x :=
        nhdsWithin_mono _ fun y hy => hy.1.ne'
      have slope_lt : ∀ᶠ y in 𝓝[Ioc x b] x, slope (branch i) x y < L :=
        (deriv.tendsto_slope.mono_left within) (Iio_mem_nhds (d_le.trans_lt KL))
      filter_upwards [slope_lt] with y hy equal
      simpa only [slope_def_field, active, equal] using hy
    · have difference := ((continuous x x_in).sub (branch_cont i x x_in)).mono subset
      have nonzero : f x - branch i x ≠ 0 := sub_ne_zero.mpr active
      have op : IsOpen {z : ℝ | z ≠ 0} := isOpen_ne
      have ev : ∀ᶠ y in 𝓝[Ioc x b] x, f y - branch i y ≠ 0 :=
        difference (op.mem_nhds nonzero)
      exact ev.mono fun y hy eq => (hy (sub_eq_zero.mpr eq)).elim
  filter_upwards [eventually_all.mpr all, self_mem_nhdsWithin] with y all_y hy
  obtain ⟨i, selected⟩ := chooses y (subset hy)
  exact all_y i selected

end Unfoldings
