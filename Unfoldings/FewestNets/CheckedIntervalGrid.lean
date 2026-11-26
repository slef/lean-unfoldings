module

public import Unfoldings.FewestNets.CheckedTrigonometry
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Fixed-point interval inputs, integer ceiling ranges, and midpoint trigonometric tests. -/

@[expose] public section

namespace Unfoldings.FewestNets

open Real

variable {D : ℕ}

namespace FixedPointInterval

/-- The exact possible integer ceiling range of an enclosure. -/
def lowerCeil (a : FixedPointInterval D) : ℤ := -((-a.lo) / D)

def upperCeil (a : FixedPointInterval D) : ℤ := -((-a.hi) / D)

private theorem ceil_div_scale (i : ℤ) : ⌈(i : ℝ) / (D : ℝ)⌉ = -((-i) / (D : ℤ)) := by
  have equal : (i : ℝ) / (D : ℝ) = -(((-i : ℤ) : ℝ) / (D : ℝ)) := by simp [neg_div]
  rw [equal, Int.ceil_neg, Int.floor_div_natCast, Int.floor_intCast]

theorem ceil_bounds (hD : 0 < D) {a : FixedPointInterval D} {x : ℝ} (hx : a.Contains x) :
    a.lowerCeil ≤ ⌈x⌉ ∧ ⌈x⌉ ≤ a.upperCeil := by
  have pos := cast_den_pos hD
  have lo : (a.lo : ℝ) / D ≤ x := (div_le_iff₀ pos).mpr hx.1
  have hi : x ≤ (a.hi : ℝ) / D := (le_div_iff₀ pos).mpr hx.2
  simpa only [lowerCeil, upperCeil, ← ceil_div_scale] using
    And.intro (Int.ceil_mono lo) (Int.ceil_mono hi)

/-- The finite list of candidate natural ceilings for the exact input. -/
def natCeilCandidates (a : FixedPointInterval D) : List ℕ :=
  List.range' a.lowerCeil.toNat (a.upperCeil.toNat + 1 - a.lowerCeil.toNat)

/-- A covered real's actual natural ceiling occurs in the enumeration. -/
theorem ceil_mem_natCeilCandidates (hD : 0 < D) {a : FixedPointInterval D} {x : ℝ} (hx : a.Contains x) :
    ⌈x⌉₊ ∈ a.natCeilCandidates := by
  have h := ceil_bounds hD hx
  have l : a.lowerCeil.toNat ≤ ⌈x⌉₊ := Int.ceil_toNat x ▸ Int.toNat_le_toNat h.1
  have u : ⌈x⌉₊ ≤ a.upperCeil.toNat := Int.ceil_toNat x ▸ Int.toNat_le_toNat h.2
  apply List.mem_range'.mpr
  exact ⟨⌈x⌉₊ - a.lowerCeil.toNat, by omega, by omega⟩

/-- The midpoint can be taken at the lower integer when the interval width is odd. -/
def midpoint (a : FixedPointInterval D) : ℤ := (a.lo + a.hi) / 2

def radius (a : FixedPointInterval D) : ℤ :=
  max (a.midpoint - a.lo) (a.hi - a.midpoint)

theorem abs_sub_midpoint_le (hD : 0 < D) {a : FixedPointInterval D} {x : ℝ} (hx : a.Contains x) :
    |x - (a.midpoint : ℝ) / D| ≤ (a.radius : ℝ) / D := by
  have dp := cast_den_pos hD
  have lo : (a.lo : ℝ) / D ≤ x := (div_le_iff₀ dp).mpr hx.1
  have hi : x ≤ (a.hi : ℝ) / D := (le_div_iff₀ dp).mpr hx.2
  have d₀ : (a.midpoint : ℝ) - (a.lo : ℝ) ≤ a.radius := by
    exact_mod_cast (le_max_left (a.midpoint - a.lo) (a.hi - a.midpoint))
  have d₁ : (a.hi : ℝ) - (a.midpoint : ℝ) ≤ a.radius := by
    exact_mod_cast (le_max_right (a.midpoint - a.lo) (a.hi - a.midpoint))
  have d₀' := div_le_div_of_nonneg_right d₀ dp.le
  have d₁' := div_le_div_of_nonneg_right d₁ dp.le
  rw [sub_div] at d₀' d₁'
  exact abs_le.mpr ⟨by linarith only [lo, d₀'], by linarith only [hi, d₁']⟩

end FixedPointInterval

namespace CheckedReal

noncomputable section

/-- Introduce a certified interval input for a symbolic parameter. -/
def enclose {x : ℝ} (a : FixedPointInterval D) (inside : a.Contains x) : CheckedReal D x where
  bounds := some a
  sound b h := Option.some.inj h ▸ inside

/-- A fixed-point coordinate already at the correct scale evaluates exactly. -/
def scaled (hD : 0 < D) (i : ℤ) : CheckedReal D ((i : ℝ) / D) :=
  enclose ⟨i, i⟩ (by
    unfold FixedPointInterval.Contains
    rw [div_mul_cancel₀ _ (FixedPointInterval.cast_den_pos hD).ne']
    exact ⟨le_rfl, le_rfl⟩)

/-- Evaluate the Taylor series only at a single midpoint and add the
one-Lipschitz error over the whole interval. -/
def centeredSin (hD : 0 < D) {x : ℝ} (a : FixedPointInterval D)
    (inside : a.Contains x) (degree : ℕ) : CheckedReal D (sin x) :=
  ((scaled hD a.midpoint).checkSin hD degree).withError (scaled hD a.radius)
    ((abs_sin_sub_sin_le x _).trans (FixedPointInterval.abs_sub_midpoint_le hD inside))

/-- The same midpoint enclosure for cosine. -/
def centeredCos (hD : 0 < D) {x : ℝ} (a : FixedPointInterval D)
    (inside : a.Contains x) (degree : ℕ) : CheckedReal D (cos x) :=
  ((scaled hD a.midpoint).checkCos hD degree).withError (scaled hD a.radius)
    ((abs_cos_sub_cos_le x _).trans (FixedPointInterval.abs_sub_midpoint_le hD inside))

/-- The computable midpoint sin enclosure on a fixed-point interval. -/
def intervalSin (hD : 0 < D) (b : FixedPointInterval D) (degree : ℕ) :
    Option (FixedPointInterval D) :=
  ((scaled hD b.midpoint).checkSin hD degree).bounds.map
    (fun out => ⟨out.lo - b.radius, out.hi + b.radius⟩)

/-- Allow the midpoint test to compose inside a larger interval expression. -/
def checkSinCentered (hD : 0 < D) {x : ℝ} (a : CheckedReal D x) (degree : ℕ) :
    CheckedReal D (sin x) :=
  a.map (fun b => intervalSin hD b degree) (by
    intro b out hx eq
    apply (centeredSin hD b hx degree).sound out
    change ((scaled hD b.midpoint).checkSin hD degree).bounds.bind
      (fun i => some ⟨i.lo - b.radius, i.hi + b.radius⟩) = some out
    cases ha : ((scaled hD b.midpoint).checkSin hD degree).bounds <;>
      simpa only [intervalSin, ha, Option.map, Option.bind] using eq)

/-- The computable midpoint cos enclosure on a fixed-point interval. -/
def intervalCos (hD : 0 < D) (b : FixedPointInterval D) (degree : ℕ) :
    Option (FixedPointInterval D) :=
  ((scaled hD b.midpoint).checkCos hD degree).bounds.map
    (fun out => ⟨out.lo - b.radius, out.hi + b.radius⟩)

/-- Allow the midpoint cosine test to compose inside a larger expression. -/
def checkCosCentered (hD : 0 < D) {x : ℝ} (a : CheckedReal D x) (degree : ℕ) :
    CheckedReal D (cos x) :=
  a.map (fun b => intervalCos hD b degree) (by
    intro b out hx eq
    apply (centeredCos hD b hx degree).sound out
    change ((scaled hD b.midpoint).checkCos hD degree).bounds.bind
      (fun i => some ⟨i.lo - b.radius, i.hi + b.radius⟩) = some out
    cases ha : ((scaled hD b.midpoint).checkCos hD degree).bounds <;>
      simpa only [intervalCos, ha, Option.map, Option.bind] using eq)

end
end CheckedReal
end Unfoldings.FewestNets
