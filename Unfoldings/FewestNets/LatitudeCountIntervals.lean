module

public import Unfoldings.FewestNets.LatitudeTriangleInterval

/-! Enclose the row counts and sum certified upper bounds for a latitude grid. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real CheckedReal

local notation "D" => countPrecision
local notation "hD" => countPrecision_pos
local notation "Q" => CheckedReal.rat countPrecision

/-- An optional certified upper endpoint at the common fixed-point scale. -/
structure CountUpper (x : ℝ) where
  bound : Option ℤ
  sound : ∀ k, bound = some k → x ≤ (k : ℝ) / D

namespace CountUpper

def ofChecked {x : ℝ} (v : CheckedCount x) : CountUpper x where
  bound := v.bounds.map FixedPointInterval.hi
  sound k e := by
    cases h : v.bounds with
    | none => simp [h] at e
    | some v' =>
      obtain rfl : v'.hi = k := Option.some.inj (by simpa only [h, Option.map_some] using e)
      exact (le_div_iff₀ (FixedPointInterval.cast_den_pos hD)).mpr (v.sound _ h).2

def add {x y : ℝ} (a : CountUpper x) (b : CountUpper y) : CountUpper (x + y) where
  bound := a.bound.bind fun i => b.bound.map fun j => i + j
  sound k e := by
    cases ha : a.bound with
    | none => simp [ha] at e
    | some i =>
      cases hb : b.bound with
      | none => simp [ha, hb] at e
      | some j =>
        obtain rfl : i + j = k := Option.some.inj (by simpa only [ha, hb, Option.bind_some, Option.map_some] using e)
        rw [Int.cast_add, add_div]
        exact add_le_add (a.sound _ ha) (b.sound _ hb)

def convert {x y : ℝ} (h : x = y) (a : CountUpper x) : CountUpper y where
  bound := a.bound
  sound i hi := h ▸ a.sound i hi

def reuse {x y : ℝ} (a : CheckedCount x) (body : CheckedCount x → CountUpper y) :
    CountUpper y where
  bound := match h : a.bounds with
    | none => none
    | some b => (body (CheckedReal.enclose b (a.sound b h))).bound
  sound b h := by
    split at h
    · simp at h
    · rename_i i eq
      exact (body (CheckedReal.enclose i (a.sound i eq))).sound b h

def sumFin : (n : ℕ) → {f : Fin n → ℝ} → (∀ i, CountUpper (f i)) → CountUpper (∑ i, f i)
  | 0, _, _ => (ofChecked ((Q 0).convert (show ((0 : ℚ) : ℝ) = 0 by norm_num))).convert (by rw [Fin.sum_univ_zero])
  | n + 1, _, bounds =>
    ((bounds 0).add (sumFin n (fun i => bounds i.succ))).convert (by rw [Fin.sum_univ_succ])

/-- Maximizing over all neighboring row counts can only increase the charge. -/
def listMax (xs : List (Option ℤ)) : Option ℤ :=
  xs.foldr (fun x y => x.bind fun i => y.map fun j => max i j) (some 0)

theorem listMax_covers {xs : List (Option ℤ)} {k : ℤ} (checked : listMax xs = some k)
    (x : Option ℤ) (mem : x ∈ xs) : ∃ j, x = some j ∧ j ≤ k := by
  induction xs generalizing k with
  | nil => simp at mem
  | cons a t ih =>
    change (a.bind fun i => (listMax t).map fun j => max i j) = some k at checked
    cases ha : a with
    | none => simp [ha] at checked
    | some i =>
      cases ht : listMax t with
      | none => simp [ha, ht] at checked
      | some j =>
        obtain rfl : max i j = k := Option.some.inj (by simpa only [ha, ht, Option.bind_some, Option.map_some] using checked)
        rcases List.mem_cons.mp mem with rfl | tail
        · exact ⟨i, ha, le_max_left _ _⟩
        · obtain ⟨z, hz, zle⟩ := ih ht tail
          exact ⟨z, hz, zle.trans (le_max_right _ _)⟩

/-- Turn a proven upper endpoint into an interval for a nonnegative quantity. -/
def nonnegative {x : ℝ} (a : CountUpper x) (hx : 0 ≤ x) : CheckedCount x where
  bounds := a.bound.map fun i => ⟨0, i⟩
  sound b hb := by
    cases h : a.bound with
    | none => simp [h] at hb
    | some i =>
      have eq : (⟨0, i⟩ : CountInterval) = b :=
        Option.some.inj (by simpa only [h, Option.map_some] using hb)
      subst b
      exact ⟨by simp only [Int.cast_zero]; positivity, (le_div_iff₀ (FixedPointInterval.cast_den_pos hD)).mp (a.sound _ h)⟩

end CountUpper

def checkCountNat (n : ℕ) : CheckedCount (n : ℝ) :=
  (Q (n : ℚ)).convert (by push_cast; rfl)

def checkCountRadius {a : ℝ} (input : CheckedCount a) : CheckedCount (radius a) :=
  ((Q 0.72).mul hD (input.sqrt hD)).convert (by norm_num [radius])

def checkCountSpacing {a : ℝ} (input : CheckedCount a) : CheckedCount (spacing a) :=
  (((Q 0.51).mul hD input).mul hD (checkCountRadius input)).convert (by norm_num [spacing])

def checkCountRho {a : ℝ} (input : CheckedCount a) : CheckedCount (AcuteLatitudeGrid.polarRadius a) :=
  ((input.sqrt hD).div hD (Q 12)).convert (by norm_num [AcuteLatitudeGrid.polarRadius])

def checkCountSpan {a : ℝ} (input : CheckedCount a) :
    CheckedCount (π - 2 * AcuteLatitudeGrid.polarRadius a) :=
  ((checkPi D).sub ((Q 2).mul hD (checkCountRho input))).convert (by norm_num)

def checkStripCount {a : ℝ} (input : CheckedCount a) :
    CheckedCount ((π - 2 * AcuteLatitudeGrid.polarRadius a) / radius a) :=
  (checkCountSpan input).div hD (checkCountRadius input)

/-- Candidate band length, before specializing to the actual band count. -/
def countBandStep (a : ℝ) (bands : ℕ) : ℝ :=
  (π - 2 * AcuteLatitudeGrid.polarRadius a) / bands

def checkCountBandStep {a : ℝ} (input : CheckedCount a) (bands : ℕ) :
    CheckedCount (countBandStep a bands) :=
  (checkCountSpan input).div hD (checkCountNat bands)

def countRowLatitude (a : ℝ) (bands j : ℕ) : ℝ :=
  AcuteLatitudeGrid.polarRadius a + j * countBandStep a bands

def checkCountRowLatitude {a : ℝ} (input : CheckedCount a) (bands j : ℕ) :
    CheckedCount (countRowLatitude a bands j) :=
  (checkCountRho input).add ((checkCountNat j).mul hD (checkCountBandStep input bands))

def checkCountPolarSize {a : ℝ} (input : CheckedCount a) :
    CheckedCount (2 * π * sin (AcuteLatitudeGrid.polarRadius a) / (0.6 * spacing a)) := by
  let numerator := (((Q 2).mul hD (checkPi D)).mul hD ((checkCountRho input).checkSinCentered hD 24))
  exact (numerator.div hD ((Q 0.6).mul hD (checkCountSpacing input))).convert (by norm_num)

def checkCountInteriorSize {a : ℝ} (input : CheckedCount a) (bands j : ℕ) :
    CheckedCount (2 * π * sin (countRowLatitude a bands j) / spacing a) := by
  let numerator := (((Q 2).mul hD (checkPi D)).mul hD ((checkCountRowLatitude input bands j).checkSinCentered hD 24))
  exact (numerator.div hD (checkCountSpacing input)).convert (by norm_num)

def checkedStripCounts {a : ℝ} (input : CheckedCount a) : Option (List ℕ) :=
  (checkStripCount input).bounds.map FixedPointInterval.natCeilCandidates

theorem checkedStripCounts_covers {a : ℝ} (input : CheckedCount a) {xs : List ℕ}
    (checked : checkedStripCounts input = some xs) : stripCount a ∈ xs := by
  unfold checkedStripCounts at checked
  cases h : (checkStripCount input).bounds with
  | none => simp [h] at checked
  | some out =>
    have eq := Option.some.inj (by simpa only [h, Option.map_some] using checked :
      some out.natCeilCandidates = some xs)
    rw [← eq]
    exact FixedPointInterval.ceil_mem_natCeilCandidates hD ((checkStripCount input).sound _ h)

def checkedRowCounts {a : ℝ} (input : CheckedCount a) (bands j : ℕ) : Option (List ℕ) :=
  if j = 0 ∨ j = bands then
    (checkCountPolarSize input).bounds.map fun i => i.natCeilCandidates.map (max 6)
  else
    (checkCountInteriorSize input bands j).bounds.map FixedPointInterval.natCeilCandidates

theorem checkedRowCounts_covers {a : ℝ} (input : CheckedCount a) (j : ℕ) {xs : List ℕ}
    (checked : checkedRowCounts input (stripCount a) j = some xs) : rowSize a j ∈ xs := by
  unfold checkedRowCounts rowSize at *
  by_cases pol : j = 0 ∨ j = stripCount a
  · simp only [ite_eq_left pol] at checked ⊢
    cases h : (checkCountPolarSize input).bounds with
    | none => simp [h] at checked
    | some out =>
      have eq := Option.some.inj (by simpa only [h, Option.map_some] using checked :
        some (out.natCeilCandidates.map (max 6)) = some xs)
      rw [← eq]
      exact List.mem_map.mpr ⟨_, FixedPointInterval.ceil_mem_natCeilCandidates hD
        ((checkCountPolarSize input).sound _ h), rfl⟩
  · simp only [ite_eq_right pol] at checked ⊢
    cases h : (checkCountInteriorSize input (stripCount a) j).bounds with
    | none => simp [h] at checked
    | some out =>
      have eq := Option.some.inj (by simpa only [h, Option.map_some] using checked :
        some out.natCeilCandidates = some xs)
      rw [← eq]
      exact FixedPointInterval.ceil_mem_natCeilCandidates hD ((checkCountInteriorSize input _ _).sound _ h)

end Unfoldings.FewestNets.RevisedLatitudeGrid
