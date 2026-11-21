module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Tactic

/-! Sound fixed-point enclosures for the finite normal-mesh certificates. -/

@[expose] public section

namespace Unfoldings.FewestNets

/-- Integer endpoints with the same positive denominator. Separate the
computable endpoints from the proof that they enclose a given real value. -/
structure FixedPointInterval (denominator : ℕ) where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

namespace FixedPointInterval

variable {D : ℕ}

/-- Membership in scaled coordinates. -/
def Contains (a : FixedPointInterval D) (x : ℝ) : Prop :=
  (a.lo : ℝ) ≤ x * D ∧ x * D ≤ (a.hi : ℝ)

theorem cast_den_pos (hD : 0 < D) : (0 : ℝ) < D := by exact_mod_cast hD

theorem intCast_ediv_le_div {a b : ℤ} (hb : 0 < b) :
    ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  have positive : (0 : ℝ) < b := by exact_mod_cast hb
  rw [le_div_iff₀ positive]
  exact_mod_cast Int.ediv_mul_le a (ne_of_gt hb)

theorem div_le_intCast_neg_ediv_neg {a b : ℤ} (hb : 0 < b) :
    (a : ℝ) / b ≤ ((-(-a / b) : ℤ) : ℝ) := by
  have h := intCast_ediv_le_div (a := -a) hb
  push_cast at h ⊢
  rw [neg_div] at h
  linarith only [h]

/-- An exact rational input rounded outwards once. -/
def ofRat (D : ℕ) (r : ℚ) : FixedPointInterval D :=
  ⟨r.num * D / r.den, - (-(r.num * D) / r.den)⟩

theorem contains_ofRat (r : ℚ) : (ofRat D r).Contains (r : ℝ) := by
  have den : (0 : ℤ) < r.den := by exact_mod_cast r.den_pos
  have eq : ((r.num * (D : ℤ) : ℤ) : ℝ) / (r.den : ℝ) = (r : ℝ) * D := by
    push_cast
    rw [← div_mul_eq_mul_div, Rat.cast_def]
  exact ⟨(intCast_ediv_le_div den).trans_eq eq,
    eq.symm.le.trans (div_le_intCast_neg_ediv_neg den)⟩

/-- An interval with endpoints already at the target scale. -/
def add (a b : FixedPointInterval D) : FixedPointInterval D := ⟨a.lo + b.lo, a.hi + b.hi⟩

def neg (a : FixedPointInterval D) : FixedPointInterval D := ⟨-a.hi, -a.lo⟩

def sub (a b : FixedPointInterval D) : FixedPointInterval D := a.add b.neg

theorem contains_add {a b : FixedPointInterval D} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.add b).Contains (x + y) := by
  simpa [Contains, add, add_mul] using
    And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem contains_neg {a : FixedPointInterval D} {x : ℝ} (hx : a.Contains x) :
    a.neg.Contains (-x) := by
  simpa [Contains, neg] using And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

theorem contains_sub {a b : FixedPointInterval D} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.sub b).Contains (x - y) := by
  simpa [sub, sub_eq_add_neg] using contains_add hx (contains_neg hy)

/-- Enclose the minimum of two enclosed reals. -/
def minimum (a b : FixedPointInterval D) : FixedPointInterval D :=
  ⟨min a.lo b.lo, min a.hi b.hi⟩

/-- Enclose the maximum of two enclosed reals. -/
def maximum (a b : FixedPointInterval D) : FixedPointInterval D :=
  ⟨max a.lo b.lo, max a.hi b.hi⟩

theorem contains_minimum (hD : 0 < D) {a b : FixedPointInterval D} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.minimum b).Contains (min x y) := by
  have scale := min_mul_of_nonneg x y (cast_den_pos hD).le
  simpa only [Contains, minimum, Int.cast_min, scale] using
    And.intro (min_le_min hx.1 hy.1) (min_le_min hx.2 hy.2)

theorem contains_maximum (hD : 0 < D) {a b : FixedPointInterval D} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.maximum b).Contains (max x y) := by
  have scale := max_mul_of_nonneg x y (cast_den_pos hD).le
  simpa only [Contains, maximum, Int.cast_max, scale] using
    And.intro (max_le_max hx.1 hy.1) (max_le_max hx.2 hy.2)

private theorem rect_bounds {l u m v x y : ℝ}
    (hl : l ≤ x) (hu : x ≤ u) (hm : m ≤ y) (hv : y ≤ v) :
    min (min (l * m) (l * v)) (min (u * m) (u * v)) ≤ x * y ∧
      x * y ≤ max (max (l * m) (l * v)) (max (u * m) (u * v)) := by
  have left (z : ℝ) : min (z * m) (z * v) ≤ z * y ∧ z * y ≤ max (z * m) (z * v) := by
    obtain hz | hz := le_total 0 z
    · exact ⟨(min_le_left ..).trans (mul_le_mul_of_nonneg_left hm hz),
        (mul_le_mul_of_nonneg_left hv hz).trans (le_max_right ..)⟩
    · exact ⟨(min_le_right ..).trans (mul_le_mul_of_nonpos_left hv hz),
        (mul_le_mul_of_nonpos_left hm hz).trans (le_max_left ..)⟩
  obtain hy | hy := le_total 0 y
  · exact ⟨(min_le_left ..).trans ((left l).1.trans (mul_le_mul_of_nonneg_right hl hy)),
      (mul_le_mul_of_nonneg_right hu hy).trans ((left u).2.trans (le_max_right ..))⟩
  · exact ⟨(min_le_right ..).trans ((left u).1.trans (mul_le_mul_of_nonpos_right hu hy)),
      (mul_le_mul_of_nonpos_right hl hy).trans ((left l).2.trans (le_max_left ..))⟩

/-- Multiply using the four corner products and round only the extremal results. -/
def mul (a b : FixedPointInterval D) : FixedPointInterval D :=
  let ll := a.lo * b.lo
  let lh := a.lo * b.hi
  let hl := a.hi * b.lo
  let hh := a.hi * b.hi
  ⟨min (min ll lh) (min hl hh) / D, - (-(max (max ll lh) (max hl hh)) / D)⟩

theorem contains_mul (hD : 0 < D) {a b : FixedPointInterval D} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.mul b).Contains (x * y) := by
  have positive := cast_den_pos hD
  have integral : (0 : ℤ) < D := by exact_mod_cast hD
  obtain ⟨lower, upper⟩ := rect_bounds hx.1 hx.2 hy.1 hy.2
  unfold Contains mul
  refine ⟨(intCast_ediv_le_div integral).trans ?_,
    le_trans ?_ (div_le_intCast_neg_ediv_neg integral)⟩
  · push_cast
    rw [div_le_iff₀ positive]
    convert lower using 1
    ring
  · push_cast
    rw [le_div_iff₀ positive]
    convert upper using 1
    ring

/-- Reciprocal enclosure for positive endpoints. -/
def invPositive (a : FixedPointInterval D) : FixedPointInterval D :=
  ⟨(D : ℤ) ^ 2 / a.hi, - (-((D : ℤ) ^ 2) / a.lo)⟩

private theorem contains_invPositive (hD : 0 < D) {a : FixedPointInterval D} {x : ℝ}
    (hx : a.Contains x) (positive : 0 < a.lo) : a.invPositive.Contains x⁻¹ := by
  have scale := cast_den_pos hD
  have l : (0 : ℝ) < a.lo := by exact_mod_cast positive
  have m := l.trans_le hx.1
  have u := m.trans_le hx.2
  have rounded_lo := intCast_ediv_le_div (a := (D : ℤ) ^ 2) (by exact_mod_cast u : 0 < a.hi)
  have rounded_hi := div_le_intCast_neg_ediv_neg (a := (D : ℤ) ^ 2) positive
  have central : (D : ℝ) ^ 2 / (x * D) = x⁻¹ * D := by
    have h : x ≠ 0 := ((mul_pos_iff_of_pos_right scale).mp m).ne'
    field_simp
  change _ ≤ x⁻¹ * D ∧ x⁻¹ * D ≤ _
  rw [← central]
  push_cast at rounded_lo rounded_hi
  constructor
  · exact rounded_lo.trans (div_le_div_of_nonneg_left (sq_nonneg _) m hx.2)
  · simp only [invPositive, Int.cast_neg]
    exact (div_le_div_of_nonneg_left (sq_nonneg _) l hx.1).trans rounded_hi

/-- Inversion fails if the enclosure touches zero. Negative intervals use
inversion on the reflected positive interval. -/
def inv (a : FixedPointInterval D) : Option (FixedPointInterval D) :=
  if 0 < a.lo then some a.invPositive
  else if a.hi < 0 then some a.neg.invPositive.neg
  else none

theorem contains_inv (hD : 0 < D) {a b : FixedPointInterval D} {x : ℝ}
    (hx : a.Contains x) (h : a.inv = some b) : b.Contains x⁻¹ := by
  unfold inv at h
  split at h
  · cases h
    exact contains_invPositive hD hx (by assumption)
  · split at h
    · rename_i negative
      cases h
      have pos : 0 < a.neg.lo := neg_pos.mpr negative
      simpa only [inv_neg, neg_neg] using
        contains_neg (contains_invPositive hD (contains_neg hx) pos)
    · cases h

def div (a b : FixedPointInterval D) : Option (FixedPointInterval D) :=
  b.inv.map (a.mul ·)

theorem contains_div (hD : 0 < D) {a b c : FixedPointInterval D} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) (h : a.div b = some c) : c.Contains (x / y) := by
  unfold div at h
  cases eq : b.inv with
  | none => simp [eq] at h
  | some u =>
    simp only [eq, Option.map_some, Option.some.injEq] at h
    rw [← h, div_eq_mul_inv]
    exact contains_mul hD hx (contains_inv hD hy eq)

/-- Ceiling of the square root of a natural number. -/
def ceilSqrt (n : ℕ) : ℕ :=
  let r := n.sqrt
  if r ^ 2 = n then r else r + 1

private theorem le_ceilSqrt_sq (n : ℕ) : n ≤ ceilSqrt n ^ 2 := by
  dsimp [ceilSqrt]
  split
  · exact le_of_eq (by assumption : n.sqrt ^ 2 = n).symm
  · exact (Nat.lt_succ_sqrt' n).le

/-- Rounded square-root endpoints, with failure on a negative lower endpoint. -/
def sqrt (a : FixedPointInterval D) : Option (FixedPointInterval D) :=
  if 0 ≤ a.lo then
    some ⟨Nat.sqrt (a.lo.toNat * D), ceilSqrt (a.hi.toNat * D)⟩
  else none

theorem contains_sqrt (hD : 0 < D) {a b : FixedPointInterval D} {x : ℝ}
    (hx : a.Contains x) (h : a.sqrt = some b) : b.Contains (Real.sqrt x) := by
  unfold sqrt at h
  split at h
  · rename_i nonneg
    cases h
    have scale := cast_den_pos hD
    have l : (0 : ℝ) ≤ a.lo := by exact_mod_cast nonneg
    have xD := l.trans hx.1
    have x0 := (mul_nonneg_iff_of_pos_right scale).mp xD
    have upper : 0 ≤ a.hi := by exact_mod_cast xD.trans hx.2
    have sq : (Real.sqrt x * D) ^ 2 = x * D * D := by
      rw [mul_pow, Real.sq_sqrt x0]
      ring
    have ll := Nat.sqrt_le' (a.lo.toNat * D)
    have uu := le_ceilSqrt_sq (a.hi.toNat * D)
    unfold Contains
    push_cast
    refine ⟨(sq_le_sq₀ (by positivity) (by positivity)).mp ?_,
      (sq_le_sq₀ (by positivity) (by positivity)).mp ?_⟩
    · rw [sq]
      have casted : (Nat.sqrt (a.lo.toNat * D) : ℝ) ^ 2 ≤ (a.lo.toNat : ℝ) * D := by
        exact_mod_cast ll
      have endpoint : (a.lo.toNat : ℝ) = a.lo := by
        exact_mod_cast Int.toNat_of_nonneg nonneg
      rw [endpoint] at casted
      exact casted.trans (mul_le_mul_of_nonneg_right hx.1 scale.le)
    · rw [sq]
      have casted : (a.hi.toNat : ℝ) * D ≤ (ceilSqrt (a.hi.toNat * D) : ℝ) ^ 2 := by
        exact_mod_cast uu
      have endpoint : (a.hi.toNat : ℝ) = a.hi := by
        exact_mod_cast Int.toNat_of_nonneg upper
      rw [endpoint] at casted
      exact (mul_le_mul_of_nonneg_right hx.2 scale.le).trans casted
  · cases h

/-- An integer sign test certifies strict positivity of the enclosed real. -/
theorem positive_of_lo_pos (hD : 0 < D) {a : FixedPointInterval D} {x : ℝ}
    (hx : a.Contains x) (h : 0 < a.lo) : 0 < x := by
  have hl : (0 : ℝ) < a.lo := by exact_mod_cast h
  exact (mul_pos_iff_of_pos_right (cast_den_pos hD)).mp (hl.trans_le hx.1)

/-- Disjoint scaled intervals certify the corresponding strict real comparison. -/
theorem lt_of_hi_lt_lo (hD : 0 < D) {a b : FixedPointInterval D} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) (h : a.hi < b.lo) : x < y := by
  have apart : (a.hi : ℝ) < b.lo := by exact_mod_cast h
  exact lt_of_mul_lt_mul_right (hx.2.trans_lt (apart.trans_le hy.1)) (cast_den_pos hD).le

/-- Use the known nonnegativity of squares to avoid a negative lower bound. -/
def square (a : FixedPointInterval D) : FixedPointInterval D :=
  (a.mul a).maximum (ofRat D 0)

theorem contains_square (hD : 0 < D) {a : FixedPointInterval D} {x : ℝ}
    (hx : a.Contains x) : a.square.Contains (x ^ 2) := by
  have hz : (ofRat D 0).Contains (0 : ℝ) := by simpa using contains_ofRat (D := D) 0
  simpa only [square, ← pow_two, max_eq_left (sq_nonneg x)] using
    contains_maximum hD (contains_mul hD hx hx) hz

/-- Use the known nonnegativity of absolute values to tighten the enclosure. -/
def abs (a : FixedPointInterval D) : FixedPointInterval D :=
  (a.maximum a.neg).maximum (ofRat D 0)

theorem contains_abs (hD : 0 < D) {a : FixedPointInterval D} {x : ℝ}
    (hx : a.Contains x) : a.abs.Contains |x| := by
  have hz : (ofRat D 0).Contains (0 : ℝ) := by simpa using contains_ofRat (D := D) 0
  simpa only [abs, ← abs_eq_max_neg, max_eq_left (abs_nonneg x)] using
    contains_maximum hD (contains_maximum hD hx (contains_neg hx)) hz

end FixedPointInterval
end Unfoldings.FewestNets
