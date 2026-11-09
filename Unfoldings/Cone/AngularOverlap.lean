module

public import Unfoldings.Cone.AngularImages
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Set.Infinite

/-!
# The exact nonoverlap criterion for slit angular fans

Above one full turn, choose a heading and its translate by a full turn away
from the finitely many piece banks. They belong to distinct open piece images
at every prescribed positive radius. Together with the forward bound, this
gives nonoverlap exactly up to and including one full turn.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n)

/-- At a full turn the two outer banks have the same developed points. -/
theorem outer_banks_coincide (full : A.totalAngle = 2 * Real.pi) (r : ℝ≥0) :
    A.place (Fin.last n) (A.finish (Fin.last n) r) = A.place 0 (A.start 0 r) := by
  have total : A.heading (Fin.last n).castSucc + A.angle (Fin.last n) = A.totalAngle := by
    rw [← A.heading_succ, Fin.succ_last, A.heading_last]
  have zero : A.heading (0 : Fin (n + 1)).castSucc = 0 := A.heading_zero
  change polarRay (A.heading (Fin.last n).castSucc) *
    ((r : ℝ) • polarRay (A.angle (Fin.last n))) =
      polarRay (A.heading (0 : Fin (n + 1)).castSucc) * (r : ℂ)
  rw [zero, polarRay_zero, one_mul, Complex.real_smul]
  calc
    _ = (r : ℂ) * polarRay
        (A.heading (Fin.last n).castSucc + A.angle (Fin.last n)) := by
      rw [polarRay_add]
      ring
    _ = _ := by rw [total, full]; simp [polarRay]

/-- A heading strictly inside the total interval and off all banks lies in an open piece. -/
theorem exists_heading_piece (θ : ℝ) (inside : θ ∈ Set.Ioo 0 A.totalAngle)
    (off_banks : ∀ k, θ ≠ A.heading k) :
    ∃ i : Fin (n + 1), θ ∈ Set.Ioo (A.heading i.castSucc) (A.heading i.succ) := by
  classical
  let candidates := Finset.univ.filter (fun k : Fin (n + 2) => A.heading k < θ)
  have nonempty : candidates.Nonempty := ⟨0, by simp [candidates, inside.1]⟩
  let k := candidates.max' nonempty
  have below : A.heading k < θ := (Finset.mem_filter.mp (candidates.max'_mem nonempty)).2
  have not_last : k ≠ Fin.last (n + 1) := by
    intro last
    rw [last, A.heading_last] at below
    exact lt_asymm below inside.2
  obtain ⟨i, index⟩ := Fin.eq_castSucc_of_ne_last not_last
  refine ⟨i, ?_, ?_⟩
  · rwa [index]
  · have next_bound : θ ≤ A.heading i.succ := by
      by_contra earlier
      have member : i.succ ∈ candidates := by
        simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
        exact lt_of_not_ge earlier
      have bound : i.succ ≤ k := candidates.le_max' _ member
      rw [← index] at bound
      exact (not_le_of_gt (show i.castSucc < i.succ from Fin.castSucc_lt_succ)) bound
    exact lt_of_le_of_ne next_bound (off_banks _)

/-- Above a full turn, two genuine piece interiors overlap at every positive radius. -/
theorem overlap_of_totalAngle_gt (width : 2 * Real.pi < A.totalAngle)
    (r : ℝ) (radius : 0 < r) :
    ∃ i j : Fin (n + 1), i ≠ j ∧ ∃ z : ℂ,
      ‖z‖ = r ∧ z ∈ interior (A.faceImage i) ∧ z ∈ interior (A.faceImage j) := by
  let forbidden : Set ℝ := Set.range A.heading ∪ Set.range (fun k => A.heading k - 2 * Real.pi)
  have finite : forbidden.Finite := (Set.finite_range _).union (Set.finite_range _)
  obtain ⟨θ, interval, avoids⟩ :=
    (Set.Ioo_infinite (by linarith : 0 < A.totalAngle - 2 * Real.pi)).exists_notMem_finite finite
  have θglobal : θ ∈ Set.Ioo 0 A.totalAngle := ⟨interval.1, by linarith [interval.2, Real.pi_pos]⟩
  have φglobal : θ + 2 * Real.pi ∈ Set.Ioo 0 A.totalAngle :=
    ⟨by linarith [interval.1, Real.pi_pos], by linarith [interval.2]⟩
  have θoff (k) : θ ≠ A.heading k := fun equal => avoids (Or.inl ⟨k, equal.symm⟩)
  have φoff (k) : θ + 2 * Real.pi ≠ A.heading k := by
    intro equal
    apply avoids
    exact Or.inr ⟨k, by linarith⟩
  obtain ⟨i, first⟩ := A.exists_heading_piece θ θglobal θoff
  obtain ⟨j, second⟩ := A.exists_heading_piece (θ + 2 * Real.pi) φglobal φoff
  have different : i ≠ j := by
    intro same
    subst j
    rw [A.heading_succ] at first second
    linarith [first.1, second.2, A.small i, Real.pi_pos]
  have periodic : polarRay (θ + 2 * Real.pi) = polarRay θ :=
    congrArg (fun z : Circle => (z : ℂ)) (Circle.exp_add_two_pi θ)
  refine ⟨i, j, different, (r : ℂ) * polarRay θ, ?_, ?_, ?_⟩
  · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos radius,
      norm_polarRay, mul_one]
  · exact (A.mem_interior_faceImage_iff i _).mpr ⟨r, radius, θ, first, rfl⟩
  · apply (A.mem_interior_faceImage_iff j _).mpr
    exact ⟨r, radius, θ + 2 * Real.pi, second, by rw [periodic]⟩

/-- A slit fan is nonoverlapping exactly when its total apex angle is at most a full turn. -/
theorem nonoverlapping_iff_totalAngle_le :
    A.Nonoverlapping ↔ A.totalAngle ≤ 2 * Real.pi := by
  constructor
  · intro separated
    by_contra wide
    obtain ⟨i, j, different, z, _, first, second⟩ :=
      A.overlap_of_totalAngle_gt (lt_of_not_ge wide) 1 zero_lt_one
    exact Set.disjoint_left.mp (separated different) first second
  · exact A.nonoverlapping_of_totalAngle_le

end Unfoldings.AngularFan
