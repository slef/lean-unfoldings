module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! Lipschitz planar maps have canonical continuous traces on the closure of their domain. -/

@[expose] public section

open scoped NNReal

namespace Unfoldings

theorem exists_continuous_complex_extension_of_lipschitzOnWith
    {α : Type*} [PseudoMetricSpace α] {F : α → ℂ} {s : Set α} {K : ℝ≥0}
    (bounded : LipschitzOnWith K F s) :
    ∃ G : α → ℂ, Continuous G ∧ Set.EqOn F G s := by
  have first : LipschitzOnWith K (fun x => (F x).re) s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have bound := bounded.dist_le_mul x hx y hy
    rw [dist_eq_norm] at bound
    have estimate := (Complex.abs_re_le_norm (F x - F y)).trans bound
    simpa only [Real.dist_eq, Complex.sub_re] using estimate
  have last : LipschitzOnWith K (fun x => (F x).im) s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have bound := bounded.dist_le_mul x hx y hy
    rw [dist_eq_norm] at bound
    have estimate := (Complex.abs_im_le_norm (F x - F y)).trans bound
    simpa only [Real.dist_eq, Complex.sub_im] using estimate
  obtain ⟨g, g_lipschitz, g_agrees⟩ := first.extend_real
  obtain ⟨h, h_lipschitz, h_agrees⟩ := last.extend_real
  let G := fun x => (g x : ℂ) + (h x : ℂ) * Complex.I
  refine ⟨G, (Complex.continuous_ofReal.comp g_lipschitz.continuous).add
    ((Complex.continuous_ofReal.comp h_lipschitz.continuous).mul continuous_const), ?_⟩
  intro x member
  apply Complex.ext
  · simpa only [G, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero] using g_agrees member
  · simpa only [G, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add] using h_agrees member

theorem continuous_complex_extensions_eq_on_closure {α : Type*} [TopologicalSpace α]
    {F G H : α → ℂ} {s : Set α} (Gcontinuous : Continuous G) (Hcontinuous : Continuous H)
    (first : Set.EqOn F G s) (last : Set.EqOn F H s) : Set.EqOn G H (closure s) := by
  exact closure_minimal (fun x member => (first member).symm.trans (last member))
    (isClosed_eq Gcontinuous Hcontinuous)

end Unfoldings
