module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! A real coordinate parametrizes each source circle inside a positive quadrant. -/

@[expose] public section

noncomputable section

namespace Unfoldings

def quadrantCirclePoint (center : ℂ) (radius x : ℝ) : ℂ :=
  center + ⟨x, Real.sqrt (radius ^ 2 - x ^ 2)⟩

@[simp] theorem quadrantCirclePoint_re (center : ℂ) (radius x : ℝ) :
    (quadrantCirclePoint center radius x - center).re = x := by
  simp only [quadrantCirclePoint, add_sub_cancel_left]

@[simp] theorem quadrantCirclePoint_im (center : ℂ) (radius x : ℝ) :
    (quadrantCirclePoint center radius x - center).im = Real.sqrt (radius ^ 2 - x ^ 2) := by
  simp only [quadrantCirclePoint, add_sub_cancel_left]

theorem continuous_quadrantCirclePoint (center : ℂ) (radius : ℝ) :
    Continuous (quadrantCirclePoint center radius) := by
  have parts : Continuous (fun x : ℝ => center + (x : ℂ) +
      (Real.sqrt (radius ^ 2 - x ^ 2) : ℂ) * Complex.I) := by fun_prop
  convert parts using 1
  funext x
  apply Complex.ext <;> simp [quadrantCirclePoint]

theorem norm_quadrantCirclePoint_sub (center : ℂ) {radius x : ℝ}
    (nonnegative : 0 ≤ radius) (member : x ∈ Set.Icc 0 radius) :
    ‖quadrantCirclePoint center radius x - center‖ = radius := by
  have radicand : 0 ≤ radius ^ 2 - x ^ 2 := by nlinarith [member.1, member.2]
  have square := Real.sq_sqrt radicand
  have identity (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have norm_square := identity (quadrantCirclePoint center radius x - center)
  rw [quadrantCirclePoint_re, quadrantCirclePoint_im] at norm_square
  nlinarith [norm_nonneg (quadrantCirclePoint center radius x - center)]

theorem quadrantCirclePoint_strict_quadrant_iff (center : ℂ) {radius x : ℝ}
    (positive : 0 < radius) :
    (0 < (quadrantCirclePoint center radius x - center).re ∧
      0 < (quadrantCirclePoint center radius x - center).im) ↔ x ∈ Set.Ioo 0 radius := by
  rw [quadrantCirclePoint_re, quadrantCirclePoint_im, Real.sqrt_pos]
  constructor
  · rintro ⟨horizontal, radicand⟩
    exact ⟨horizontal, by nlinarith⟩
  · rintro ⟨horizontal, upper⟩
    exact ⟨horizontal, by nlinarith⟩

/-- Every positive-quadrant circle point is represented by its horizontal coordinate. -/
theorem quadrantCirclePoint_eq_of_norm (center : ℂ) {radius : ℝ} {z : ℂ}
    (quadrant : 0 ≤ (z - center).re ∧ 0 ≤ (z - center).im)
    (size : ‖z - center‖ = radius) :
    quadrantCirclePoint center radius (z - center).re = z := by
  let w := z - center
  have identity : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have radicand : radius ^ 2 - w.re ^ 2 = w.im ^ 2 := by
    change ‖w‖ = radius at size
    rw [size] at identity
    linarith
  have root : Real.sqrt (radius ^ 2 - w.re ^ 2) = w.im := by
    rw [radicand, Real.sqrt_sq_eq_abs, abs_of_nonneg quadrant.2]
  have vector : (⟨w.re, Real.sqrt (radius ^ 2 - w.re ^ 2)⟩ : ℂ) = w := Complex.ext rfl root
  change center + (⟨w.re, Real.sqrt (radius ^ 2 - w.re ^ 2)⟩ : ℂ) = z
  rw [vector]
  dsimp only [w]
  abel

theorem quadrantCirclePoint_preimage_subset {U : Set ℂ} (center : ℂ) {radius : ℝ}
    (positive : 0 < radius)
    (quadrant : ∀ z ∈ U, 0 < (z - center).re ∧ 0 < (z - center).im) :
    quadrantCirclePoint center radius ⁻¹' U ⊆ Set.Ioo 0 radius :=
  fun _ member => (quadrantCirclePoint_strict_quadrant_iff center positive).mp (quadrant _ member)

end Unfoldings
