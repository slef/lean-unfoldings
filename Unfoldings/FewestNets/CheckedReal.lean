module

public import Unfoldings.FewestNets.FixedPointInterval

/-! Composable real enclosures with kernel-computable comparison tests. -/

@[expose] public section

namespace Unfoldings.FewestNets

noncomputable section

/-- An optional fixed-point enclosure of a particular real expression. The
index carries the exact meaning, and computing the endpoints does not evaluate
that real. Failure is available for unsafe interval operations. -/
structure CheckedReal (D : ℕ) (x : ℝ) where
  bounds : Option (FixedPointInterval D)
  sound : ∀ i, bounds = some i → i.Contains x

namespace CheckedReal

variable {D : ℕ} {x y : ℝ}

/-- Extend an enclosure by a validated unary operation. -/
def map {z : ℝ} (check : FixedPointInterval D → Option (FixedPointInterval D))
    (valid : ∀ {a b}, a.Contains x → check a = some b → b.Contains z)
    (v : CheckedReal D x) : CheckedReal D z where
  bounds := v.bounds.bind check
  sound b hb := by
    cases h : v.bounds with
    | none => simp [h] at hb
    | some a => exact valid (v.sound a h) (by simpa [h] using hb)

/-- Extend two enclosures by a validated binary operation. -/
def map₂ {z : ℝ}
    (check : FixedPointInterval D → FixedPointInterval D → Option (FixedPointInterval D))
    (valid : ∀ {a b c}, a.Contains x → b.Contains y → check a b = some c → c.Contains z)
    (v : CheckedReal D x) (w : CheckedReal D y) : CheckedReal D z where
  bounds := v.bounds.bind fun a => w.bounds.bind (check a)
  sound c hc := by
    cases hv : v.bounds with
    | none => simp [hv] at hc
    | some a =>
      cases hw : w.bounds with
      | none => simp [hv, hw] at hc
      | some b => exact valid (v.sound a hv) (w.sound b hw) (by simpa [hv, hw] using hc)

/-- The real cast of a rational is enclosed by rounding its scaled numerator. -/
def rat (D : ℕ) (q : ℚ) : CheckedReal D (q : ℝ) where
  bounds := some (FixedPointInterval.ofRat D q)
  sound _ h := (Option.some.inj h) ▸ FixedPointInterval.contains_ofRat q

/-- Change the real expression indexing an enclosure without changing its endpoints. -/
def convert {x y : ℝ} (h : x = y) (v : CheckedReal D x) : CheckedReal D y where
  bounds := v.bounds
  sound b hb := h ▸ v.sound b hb

def add (a : CheckedReal D x) (b : CheckedReal D y) : CheckedReal D (x + y) :=
  map₂ (fun i j => some (i.add j))
    (fun ha hb h => Option.some.inj h ▸ FixedPointInterval.contains_add ha hb) a b

def neg (a : CheckedReal D x) : CheckedReal D (-x) :=
  map (fun i => some i.neg)
    (fun ha h => Option.some.inj h ▸ FixedPointInterval.contains_neg ha) a

def sub (a : CheckedReal D x) (b : CheckedReal D y) : CheckedReal D (x - y) :=
  map₂ (fun i j => some (i.sub j))
    (fun ha hb h => Option.some.inj h ▸ FixedPointInterval.contains_sub ha hb) a b

def mul (hD : 0 < D) (a : CheckedReal D x) (b : CheckedReal D y) :
    CheckedReal D (x * y) :=
  map₂ (fun i j => some (i.mul j))
    (fun ha hb h => Option.some.inj h ▸ FixedPointInterval.contains_mul hD ha hb) a b

def div (hD : 0 < D) (a : CheckedReal D x) (b : CheckedReal D y) :
    CheckedReal D (x / y) :=
  map₂ FixedPointInterval.div (FixedPointInterval.contains_div hD) a b

def sqrt (hD : 0 < D) (a : CheckedReal D x) : CheckedReal D (Real.sqrt x) :=
  map FixedPointInterval.sqrt (FixedPointInterval.contains_sqrt hD) a

def square (hD : 0 < D) (a : CheckedReal D x) : CheckedReal D (x ^ 2) :=
  map (fun i => some i.square)
    (fun ha h => Option.some.inj h ▸ FixedPointInterval.contains_square hD ha) a

def abs (hD : 0 < D) (a : CheckedReal D x) : CheckedReal D |x| :=
  map (fun i => some i.abs)
    (fun ha h => Option.some.inj h ▸ FixedPointInterval.contains_abs hD ha) a

def minimum (hD : 0 < D) (a : CheckedReal D x) (b : CheckedReal D y) :
    CheckedReal D (min x y) :=
  map₂ (fun i j => some (i.minimum j))
    (fun ha hb h => Option.some.inj h ▸ FixedPointInterval.contains_minimum hD ha hb) a b

def maximum (hD : 0 < D) (a : CheckedReal D x) (b : CheckedReal D y) :
    CheckedReal D (max x y) :=
  map₂ (fun i j => some (i.maximum j))
    (fun ha hb h => Option.some.inj h ▸ FixedPointInterval.contains_maximum hD ha hb) a b

/-- Test that the lower endpoint is positive. -/
def isPositive (a : CheckedReal D x) : Bool :=
  a.bounds.any fun i => decide (0 < i.lo)

/-- Test that the two intervals are strictly ordered. -/
def isLT (a : CheckedReal D x) (b : CheckedReal D y) : Bool :=
  a.bounds.any fun i => b.bounds.any fun j => decide (i.hi < j.lo)

theorem positive_of_isPositive (hD : 0 < D) (a : CheckedReal D x)
    (h : a.isPositive = true) : 0 < x := by
  cases ha : a.bounds with
  | none => simp [isPositive, ha] at h
  | some i =>
    have pos : 0 < i.lo := by simpa [isPositive, ha] using h
    exact FixedPointInterval.positive_of_lo_pos hD (a.sound i ha) pos

theorem lt_of_isLT (hD : 0 < D) (a : CheckedReal D x) (b : CheckedReal D y)
    (h : a.isLT b = true) : x < y := by
  cases ha : a.bounds with
  | none => simp [isLT, ha] at h
  | some i =>
    cases hb : b.bounds with
    | none => simp [isLT, ha, hb] at h
    | some j =>
      have lt : i.hi < j.lo := by simpa [isLT, ha, hb] using h
      exact FixedPointInterval.lt_of_hi_lt_lo hD (a.sound i ha) (b.sound j hb) lt

end CheckedReal
end

end Unfoldings.FewestNets
