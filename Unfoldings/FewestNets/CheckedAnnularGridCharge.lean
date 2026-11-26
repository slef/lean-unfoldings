module

public import Unfoldings.FewestNets.LatitudeCountIntervals
public import Unfoldings.FewestNets.LatitudeChargeGeometry
public import Unfoldings.FewestNets.ClosedLatitudeApexIndex

/-! The checker maximizes independently over candidate row sizes in each band. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real CheckedReal

local notation "D" => countPrecision
local notation "hD" => countPrecision_pos
local notation "Q" => CheckedReal.rat countPrecision

def checkSweepHalf (m : ℕ) : CheckedCount (π / m) :=
  ((checkPi D).mul hD (Q (1 / (m : ℚ)))).convert (by push_cast; ring)

def checkSweepOffset (m n i k : ℕ) : CheckedCount (sweepOffset m n i k) :=
  let ratio : ℚ := (2 * (k : ℚ) * m - (2 * (i : ℚ) + 1) * n) / ((m : ℚ) * n)
  ((checkPi D).mul hD (Q ratio)).convert (by dsimp [ratio, sweepOffset]; push_cast; rfl)

def checkSweepTriangle {lo hi step : ℝ} (sl : CheckedCount (sin lo)) (cl : CheckedCount (cos lo))
    (su : CheckedCount (sin hi)) (cu : CheckedCount (cos hi))
    (sd : CheckedCount (sin step)) (ds : CheckedCount (sin (step / 2)))
    {m n : ℕ} (k : Fin m ⊕ Fin n) :
    CheckedCount (sweepTriangleCharge lo hi step k) :=
  match k with
  | .inl i =>
    (checkLatitudeTriangleOfTrig sl cl su cu sd ds (checkSweepHalf m)
      (checkSweepOffset m n i (LatitudeRings.midpointPredecessors m n i true)) false).convert
      (by simp only [sweepTriangleCharge, LatitudeRings.oppositeIndex_inl_formula])
  | .inr i =>
    (checkLatitudeTriangleOfTrig su cu sl cl
      (sd.neg.convert (sin_neg step).symm) (ds.neg.convert (by rw [neg_div, sin_neg]))
      (checkSweepHalf n) (checkSweepOffset n m i (LatitudeRings.midpointPredecessors n m i false)) true).convert
      (by simp only [sweepTriangleCharge, LatitudeRings.oppositeIndex_inr_formula])

def bandCharge (lo hi step : ℝ) (m n : ℕ) : ℝ :=
  ∑ k : Fin m ⊕ Fin n, sweepTriangleCharge lo hi step k

def checkBandCharge {lo hi step : ℝ} (l : CheckedCount lo) (h : CheckedCount hi)
    (d : CheckedCount step) (m n : ℕ) : CountUpper (bandCharge lo hi step m n) :=
  CountUpper.reuse (l.checkSinCentered hD 24) fun sl =>
  CountUpper.reuse (l.checkCosCentered hD 24) fun cl =>
  CountUpper.reuse (h.checkSinCentered hD 24) fun su =>
  CountUpper.reuse (h.checkCosCentered hD 24) fun cu =>
  CountUpper.reuse (d.checkSinCentered hD 10) fun sd =>
  CountUpper.reuse ((d.div hD (Q 2)).checkSinCentered hD 10) fun ds =>
    let check := checkSweepTriangle sl cl su cu sd ds (m := m) (n := n)
    ((CountUpper.sumFin m (fun i => CountUpper.ofChecked (check (.inl i)))).add
      (CountUpper.sumFin n (fun i => CountUpper.ofChecked (check (.inr i))))).convert
        (by rw [bandCharge, Fintype.sum_sum_type])

def checkBandAt {a : ℝ} (input : CheckedCount a) (bands j m n : ℕ) :
    CountUpper (bandCharge (countRowLatitude a bands j) (countRowLatitude a bands (j + 1))
      (countBandStep a bands) m n) :=
  checkBandCharge (checkCountRowLatitude input bands j)
    (checkCountRowLatitude input bands (j + 1)) (checkCountBandStep input bands) m n

def checkedBandOptions {a : ℝ} (input : CheckedCount a) (bands j : ℕ) : Option ℤ := do
  let lower ← checkedRowCounts input bands j
  let upper ← checkedRowCounts input bands (j + 1)
  CountUpper.listMax (lower.flatMap fun m => upper.map fun n => (checkBandAt input bands j m n).bound)

def actualBandCharge (a : ℝ) (j : ℕ) : ℝ :=
  bandCharge (colatitude a j) (colatitude a (j + 1)) (rowStep a) (rowSize a j) (rowSize a (j + 1))

def checkActualBandCharge {a : ℝ} (input : CheckedCount a) (j : ℕ) :
    CountUpper (actualBandCharge a j) where
  bound := checkedBandOptions input (stripCount a) j
  sound k checked := by
    unfold checkedBandOptions at checked
    cases hl : checkedRowCounts input (stripCount a) j with
    | none => simp [hl] at checked
    | some lower =>
      cases hu : checkedRowCounts input (stripCount a) (j + 1) with
      | none => simp [hl, hu] at checked
      | some upper =>
        simp only [hl, hu] at checked
        let m := rowSize a j
        let n := rowSize a (j + 1)
        let v := checkBandAt input (stripCount a) j m n
        have mem : v.bound ∈ lower.flatMap (fun r => upper.map fun s =>
            (checkBandAt input (stripCount a) j r s).bound) := by
          apply List.mem_flatMap.mpr
          exact ⟨m, checkedRowCounts_covers input j hl, List.mem_map.mpr
            ⟨n, checkedRowCounts_covers input (j + 1) hu, rfl⟩⟩
        obtain ⟨u, hu', huk⟩ := CountUpper.listMax_covers checked _ mem
        exact (v.sound u hu').trans (div_le_div_of_nonneg_right (by exact_mod_cast huk)
          (FixedPointInterval.cast_den_pos hD).le)

def gridCharge (a : ℝ) : ℝ := ∑ j : Fin (stripCount a), actualBandCharge a j

/-- The checked sum is over exactly the spherical annular triangles. -/
theorem gridCharge_eq_sum {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    gridCharge a = ∑ i : AnnularTriangle a, annularAlgebraicCharge i := by
  rw [gridCharge, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  unfold actualBandCharge bandCharge
  let pass := LatitudeRings.sweepOrder (rowSize a j) (rowSize a (j.val + 1))
  rw [← Equiv.sum_comp pass]
  apply Finset.sum_congr rfl
  intro k _
  have row₁ : rowSize a j ≠ 0 := (rowSize_pos positive small j.isLt.le).ne'
  have row₂ : rowSize a (j.val + 1) ≠ 0 := (rowSize_pos positive small (by omega)).ne'
  rw [annularAlgebraicCharge_eq_sweep ⟨j, k⟩ row₁ row₂]
  have d : colatitude a (j.val + 1) - colatitude a j = rowStep a := by
    unfold colatitude
    push_cast
    ring
  change _ = sweepTriangleCharge _ _ (colatitude a (j.val + 1) - colatitude a j) (pass k)
  rw [d]

/-- Computation at an arbitrary band-count candidate. -/
def checkedGridAt {a : ℝ} (input : CheckedCount a) (bands : ℕ) : Option ℤ :=
  ((List.finRange bands).map fun (j : Fin bands) => checkedBandOptions input bands j.val).foldr
    (fun x y => x.bind fun i => y.map fun j => i + j) (some 0)

private theorem sumFin_bound_eq {n : ℕ} {f : Fin n → ℝ} (v : ∀ i, CountUpper (f i)) :
    (CountUpper.sumFin n v).bound =
      ((List.finRange n).map fun i => (v i).bound).foldr
        (fun x y => x.bind fun i => y.map fun j => i + j) (some 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.finRange_succ, List.map_cons, List.map_map, List.foldr_cons, Function.comp_def]
    change ((v 0).bound.bind fun i => (CountUpper.sumFin n (fun j => v j.succ)).bound.map
      (fun j => i + j)) = _
    rw [ih]

/-- The overall annular sum retains a single upper endpoint. -/
def checkGridCharge {a : ℝ} (input : CheckedCount a) : CountUpper (gridCharge a) where
  bound := do
    let candidates ← checkedStripCounts input
    CountUpper.listMax (candidates.map (checkedGridAt input))
  sound k check := by
    cases hs : checkedStripCounts input with
    | none => simp [hs] at check
    | some candidates =>
      simp only [hs] at check
      obtain ⟨r, hr, hle⟩ := CountUpper.listMax_covers check _
        (List.mem_map.mpr ⟨stripCount a, checkedStripCounts_covers input hs, rfl⟩)
      let v := CountUpper.sumFin (stripCount a) (fun j => checkActualBandCharge input j)
      have eq : v.bound = checkedGridAt input (stripCount a) := by
        unfold v checkedGridAt
        rw [sumFin_bound_eq]
        rfl
      exact (v.sound r (eq.trans hr)).trans (div_le_div_of_nonneg_right (by exact_mod_cast hle)
        (FixedPointInterval.cast_den_pos hD).le)

end Unfoldings.FewestNets.RevisedLatitudeGrid
