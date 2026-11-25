module

public import Unfoldings.FewestNets.LatitudeClosestRow
public import Unfoldings.FewestNets.LatitudeStripTriangles

/-! The sorted midpoint schedule constructs the actual strip triangles. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

variable {m n : ℕ} (step : Fin (m + n) ≃ (Fin m ⊕ Fin n))

/-- Position of a lower-row midpoint in the merged schedule. -/
def lowerRank (i : Fin m) : Fin (m + n) := step.symm (Sum.inl i)

/-- Position of an upper-row midpoint in the merged schedule. -/
def upperRank (i : Fin n) : Fin (m + n) := step.symm (Sum.inr i)

variable (sorted : StrictMono (midpointKey ∘ step))

include sorted in
theorem lowerRank_strictMono : StrictMono (lowerRank step) := by
  intro i j before
  apply sorted.lt_iff_lt.mp
  simp only [Function.comp_apply, lowerRank, Equiv.apply_symm_apply]
  exact Prod.Lex.lt_iff.mpr (Or.inl (rowMidpoint_strictMono m before))

include sorted in
theorem upperRank_strictMono : StrictMono (upperRank step) := by
  intro i j before
  apply sorted.lt_iff_lt.mp
  simp only [Function.comp_apply, upperRank, Equiv.apply_symm_apply]
  exact Prod.Lex.lt_iff.mpr (Or.inl (rowMidpoint_strictMono n before))

/-- A strictly ordered row has advanced exactly to the index of its next edge. -/
theorem rowProgress_at_rank {k total : ℕ} (rank : Fin k → Fin total)
    (strict : StrictMono rank) (i : Fin k) : rowProgress rank (rank i).val = i.val := by
  have eq : (Finset.univ.filter fun j => (rank j).val < (rank i).val) = Finset.Iio i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact strict.lt_iff_lt
  rw [rowProgress, eq, Fin.card_Iio]

private theorem rowMidpoint_in_strip {k : ℕ} (i : Fin k) : rowMidpoint k i ∈ Set.Icc 0 (2 * π) := by
  have k_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have up : (i.val : ℝ) + 1 ≤ k := by exact_mod_cast i.isLt
  unfold rowMidpoint
  refine ⟨by positivity, (div_le_iff₀ k_pos).mpr ?_⟩
  exact mul_le_mul_of_nonneg_left (by linarith only [up]) (by positivity)

private def midpointLongitude : Fin m ⊕ Fin n → ℝ :=
  fun e => (ofLex (midpointKey e)).1

include sorted in
private theorem midpointLongitude_mono : Monotone (midpointLongitude ∘ step) := by
  intro i j before
  have order := sorted.monotone before
  rcases Prod.Lex.le_iff.mp order with strict | same
  · exact strict.le
  · exact same.1.le

/-- Lower sweep longitude at each cross-row edge, including the repeated seam. -/
def lowerSweepLongitude (i : Fin (m + n + 1)) : ℝ :=
  rowLongitude m (rowProgress (lowerRank step) i.val)

/-- Upper sweep longitude at each cross-row edge, including the repeated seam. -/
def upperSweepLongitude (i : Fin (m + n + 1)) : ℝ :=
  rowLongitude n (rowProgress (upperRank step) i.val)

include sorted in
/-- At a lower advance, the actual current upper site is within half its row
spacing of the lower edge midpoint. -/
theorem upperSweep_near_lower_midpoint (positive : 0 < n)
    (i : Fin (m + n)) (j : Fin m) (advance : step i = .inl j) :
    |rowMidpoint m j - upperSweepLongitude step i.castSucc| ≤ π / n := by
  apply rowProgress_closest positive (upperRank step) (upperRank_strictMono step sorted) i.val
    (rowMidpoint_in_strip j)
  · intro k earlier
    have h := midpointLongitude_mono step sorted
      (show upperRank step k ≤ i from earlier.le)
    simpa only [Function.comp_apply, upperRank, Equiv.apply_symm_apply, advance,
      midpointLongitude, midpointKey, ofLex_toLex] using h
  · intro k later
    have h := midpointLongitude_mono step sorted (show i ≤ upperRank step k from later)
    simpa only [Function.comp_apply, upperRank, Equiv.apply_symm_apply, advance,
      midpointLongitude, midpointKey, ofLex_toLex] using h

include sorted in
/-- At an upper advance, the lower site lies within half its row spacing. -/
theorem lowerSweep_near_upper_midpoint (positive : 0 < m)
    (i : Fin (m + n)) (j : Fin n) (advance : step i = .inr j) :
    |rowMidpoint n j - lowerSweepLongitude step i.castSucc| ≤ π / m := by
  apply rowProgress_closest positive (lowerRank step) (lowerRank_strictMono step sorted) i.val
    (rowMidpoint_in_strip j)
  · intro k earlier
    have h := midpointLongitude_mono step sorted
      (show lowerRank step k ≤ i from earlier.le)
    simpa only [Function.comp_apply, lowerRank, Equiv.apply_symm_apply, advance,
      midpointLongitude, midpointKey, ofLex_toLex] using h
  · intro k later
    have h := midpointLongitude_mono step sorted (show i ≤ lowerRank step k from later)
    simpa only [Function.comp_apply, lowerRank, Equiv.apply_symm_apply, advance,
      midpointLongitude, midpointKey, ofLex_toLex] using h

theorem lowerSweepLongitude_mono : Monotone (lowerSweepLongitude step) :=
  fun _ _ before => rowLongitude_mono m (rowProgress_mono (lowerRank step) before)

theorem upperSweepLongitude_mono : Monotone (upperSweepLongitude step) :=
  fun _ _ before => rowLongitude_mono n (rowProgress_mono (upperRank step) before)

include sorted in
/-- A lower advance has the consecutive lower-row vertices as its base. -/
theorem lower_sweep_triangle (i : Fin (m + n)) (j : Fin m) (advance : step i = .inl j) :
    betweenCrossRows (lowerSweepLongitude step) (upperSweepLongitude step) i =
      convexHull ℝ ({⟨upperSweepLongitude step i.castSucc, 1⟩,
        ⟨rowLongitude m j.val, 0⟩, ⟨rowLongitude m (j.val + 1), 0⟩} : Set ℂ) := by
  have index : lowerRank step j = i := by
    rw [lowerRank, ← advance, step.symm_apply_apply]
  have current := rowProgress_at_rank _ (lowerRank_strictMono step sorted) j
  have next := rowProgress_succ_eq_of_edge _ (lowerRank_strictMono step sorted).injective j
  rw [index] at current next
  have fixed : upperSweepLongitude step i.castSucc = upperSweepLongitude step i.succ := by
    unfold upperSweepLongitude
    change rowLongitude n (rowProgress (upperRank step) i.val) =
      rowLongitude n (rowProgress (upperRank step) (i.val + 1))
    rw [rowProgress_succ_eq_of_no_edge]
    intro k same
    have indices : upperRank step k = i := Fin.ext same
    have impossible := congrArg step indices
    rw [upperRank, step.apply_symm_apply, advance] at impossible
    cases impossible
  rw [betweenCrossRows_eq_lower_triangle _ _ _ (lowerSweepLongitude_mono step
    (Fin.castSucc_le_succ i)) fixed]
  simp only [lowerSweepLongitude, Fin.val_castSucc, Fin.val_succ, next, current]

include sorted in
/-- An upper advance has the consecutive upper-row vertices as its base. -/
theorem upper_sweep_triangle (i : Fin (m + n)) (j : Fin n) (advance : step i = .inr j) :
    betweenCrossRows (lowerSweepLongitude step) (upperSweepLongitude step) i =
      convexHull ℝ ({⟨lowerSweepLongitude step i.castSucc, 0⟩,
        ⟨rowLongitude n j.val, 1⟩, ⟨rowLongitude n (j.val + 1), 1⟩} : Set ℂ) := by
  have index : upperRank step j = i := by
    rw [upperRank, ← advance, step.symm_apply_apply]
  have current := rowProgress_at_rank _ (upperRank_strictMono step sorted) j
  have next := rowProgress_succ_eq_of_edge _ (upperRank_strictMono step sorted).injective j
  rw [index] at current next
  have fixed : lowerSweepLongitude step i.castSucc = lowerSweepLongitude step i.succ := by
    unfold lowerSweepLongitude
    change rowLongitude m (rowProgress (lowerRank step) i.val) =
      rowLongitude m (rowProgress (lowerRank step) (i.val + 1))
    rw [rowProgress_succ_eq_of_no_edge]
    intro k same
    have indices : lowerRank step k = i := Fin.ext same
    have impossible := congrArg step indices
    rw [lowerRank, step.apply_symm_apply, advance] at impossible
    cases impossible
  rw [betweenCrossRows_eq_upper_triangle _ _ _ (upperSweepLongitude_mono step
    (Fin.castSucc_le_succ i)) fixed]
  simp only [upperSweepLongitude, Fin.val_castSucc, Fin.val_succ, next, current]

/-- The swept parameter triangles cover the closed longitude strip. The first
and last meridians will be identified in the spherical parameterization. -/
theorem iUnion_latitude_sweep (lower_pos : 0 < m) (upper_pos : 0 < n) :
    (⋃ i, betweenCrossRows (lowerSweepLongitude step) (upperSweepLongitude step) i) =
      {z : ℂ | z.im ∈ Set.Icc (0 : ℝ) 1 ∧ z.re ∈ Set.Icc 0 (2 * π)} := by
  have finish (k : ℕ) (positive : 0 < k) : rowLongitude k k = 2 * π := by
    unfold rowLongitude
    exact mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr positive.ne')
  refine iUnion_betweenCrossRows _ _ (lowerSweepLongitude_mono step)
    (upperSweepLongitude_mono step) (by omega) 0 (2 * π) ?_ ?_ ?_ ?_
  · simp [lowerSweepLongitude, rowProgress_zero, rowLongitude]
  · simp [upperSweepLongitude, rowProgress_zero, rowLongitude]
  · simpa [lowerSweepLongitude, rowProgress_end] using finish m lower_pos
  · simpa [upperSweepLongitude, rowProgress_end] using finish n upper_pos

end Unfoldings.FewestNets
