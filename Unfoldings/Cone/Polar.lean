module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Tactic.Linarith

/-!
# Polar developments with real angular headings

Headings are real numbers, rather than angles modulo a full turn. The planar
map may therefore overlap. It is injective on positive radii and the open
angular interval exactly when its width is at most one full turn. Above that
width, collisions occur at every positive radius.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- A radially open strip whose two banks have distinct real headings. -/
abbrev PolarStrip (a b : ℝ) := Set.Ioi (0 : ℝ) × Set.Ioo a b

/-- The actual planar polar map, allowing any angular width and overlap. -/
def polarStripMap (a b : ℝ) (x : PolarStrip a b) : ℂ :=
  (x.1.val : ℂ) * (Circle.exp x.2.val : ℂ)

theorem continuous_polarStripMap (a b : ℝ) : Continuous (polarStripMap a b) :=
  (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul
    (continuous_subtype_val.comp
      (Circle.exp.continuous.comp (continuous_subtype_val.comp continuous_snd)))

theorem norm_polarStripMap (a b : ℝ) (x : PolarStrip a b) :
    ‖polarStripMap a b x‖ = x.1.val := by
  simp only [polarStripMap, norm_mul, Circle.norm_coe, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos x.1.property]

theorem polarStripMap_injective (a b : ℝ) (width : b - a ≤ 2 * Real.pi) :
    Function.Injective (polarStripMap a b) := by
  intro x y equal
  have radius : x.1 = y.1 := Subtype.ext
    ((norm_polarStripMap a b x).symm.trans
      ((congrArg norm equal).trans (norm_polarStripMap a b y)))
  have direction : Circle.exp x.2.val = Circle.exp y.2.val := by
    apply Subtype.ext
    have nonzero : (x.1.val : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt x.1.property)
    change (x.1.val : ℂ) * (Circle.exp x.2.val : ℂ) =
      (y.1.val : ℂ) * (Circle.exp y.2.val : ℂ) at equal
    rw [← radius] at equal
    exact mul_left_cancel₀ nonzero equal
  have heading : x.2 = y.2 := Subtype.ext
    (Circle.exp_injOn_Ico width
      ⟨x.2.property.1.le, x.2.property.2⟩
      ⟨y.2.property.1.le, y.2.property.2⟩ direction)
  exact Prod.ext radius heading

/-- More than one turn gives two distinct real headings with the same planar point. -/
theorem polarStripMap_collision (a b r : ℝ) (width : 2 * Real.pi < b - a)
    (positive : 0 < r) :
    ∃ x y : PolarStrip a b, x ≠ y ∧ x.1.val = r ∧ y.1.val = r ∧
      polarStripMap a b x = polarStripMap a b y := by
  let θ := a + (b - a - 2 * Real.pi) / 2
  have first : a < θ ∧ θ < b := by dsimp [θ]; constructor <;> linarith [Real.pi_pos]
  have second : a < θ + 2 * Real.pi ∧ θ + 2 * Real.pi < b := by
    dsimp [θ]
    constructor <;> linarith [Real.pi_pos]
  let x : PolarStrip a b := (⟨r, positive⟩, ⟨θ, first⟩)
  let y : PolarStrip a b := (⟨r, positive⟩, ⟨θ + 2 * Real.pi, second⟩)
  refine ⟨x, y, ?_, rfl, rfl, ?_⟩
  · intro equal
    have headings : θ = θ + 2 * Real.pi := congrArg (fun z : PolarStrip a b => z.2.val) equal
    linarith [Real.pi_pos]
  · change (r : ℂ) * (Circle.exp θ : ℂ) =
      (r : ℂ) * (Circle.exp (θ + 2 * Real.pi) : ℂ)
    rw [Circle.exp_add_two_pi]

/-- At exactly one turn, the terminal banks may coincide, but the open strip stays injective. -/
theorem polarStripMap_injective_iff (a b : ℝ) :
    Function.Injective (polarStripMap a b) ↔ b - a ≤ 2 * Real.pi := by
  constructor
  · intro injective
    by_contra wide
    obtain ⟨x, y, different, _, _, equal⟩ :=
      polarStripMap_collision a b 1 (lt_of_not_ge wide) zero_lt_one
    exact different (injective equal)
  · exact polarStripMap_injective a b

end Unfoldings
