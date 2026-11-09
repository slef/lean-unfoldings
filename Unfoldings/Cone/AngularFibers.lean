module

public import Unfoldings.Cone.AngularCoordinates
public import Unfoldings.Cone.PolarEquality

/-!
# Closed-bank fibers of angular developments

A shared real heading belongs either to one piece or to the two consecutive
pieces at their common bank. The corresponding points are already identified
in the intrinsic slit fan metric.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n)

theorem exists_place_polar (i : Fin (n + 1)) (x : A.Cell i) :
    ∃ r : ℝ≥0, ∃ θ ∈ Set.Icc (A.heading i.castSucc) (A.heading i.succ),
      A.place i x = (r : ℂ) * polarRay θ :=
  (A.mem_faceImage_iff i (A.place i x)).mp ⟨x.val, x.property, rfl⟩

theorem faceMap_eq_origin_of_place_zero (i : Fin (n + 1)) (x : A.Cell i)
    (zero : A.place i x = 0) : A.faceMap i x = A.origin := by
  have same : x = A.start i 0 := (A.place_isometry i).injective (by
    rw [zero, A.place_start]
    simp)
  rw [same, A.faceMap_start_zero]

theorem faceMap_eq_of_same_heading_of_lt (i j : Fin (n + 1)) (ordered : i < j)
    (x : A.Cell i) (y : A.Cell j) (r : ℝ≥0) (θ : ℝ)
    (left_bounds : θ ∈ Set.Icc (A.heading i.castSucc) (A.heading i.succ))
    (right_bounds : θ ∈ Set.Icc (A.heading j.castSucc) (A.heading j.succ))
    (left_coordinates : A.place i x = (r : ℂ) * polarRay θ)
    (right_coordinates : A.place j y = (r : ℂ) * polarRay θ) :
    A.faceMap i x = A.faceMap j y := by
  have gap := A.heading_strictMono.monotone
    (show i.succ ≤ j.castSucc from Nat.succ_le_of_lt ordered)
  have heads : A.heading i.succ = A.heading j.castSucc :=
    le_antisymm gap (right_bounds.1.trans left_bounds.2)
  have left_heading : θ = A.heading i.succ :=
    le_antisymm left_bounds.2 (gap.trans right_bounds.1)
  have right_heading : θ = A.heading j.castSucc := left_heading.trans heads
  have not_last : i ≠ Fin.last n := by
    intro last
    rw [last] at ordered
    exact (not_lt_of_ge (Fin.le_last j)) ordered
  obtain ⟨k, index⟩ := Fin.eq_castSucc_of_ne_last not_last
  subst i
  have next_index : j = k.succ := by
    apply Fin.castSucc_injective
    have indices := A.heading_strictMono.injective heads
    simpa only [Fin.succ_castSucc] using indices.symm
  subst j
  have left_bank : x = A.finish k.castSucc r := (A.place_isometry _).injective (by
    rw [left_coordinates, left_heading]
    exact (A.place_finish k.castSucc r).symm)
  have right_bank : y = A.start k.succ r := (A.place_isometry _).injective (by
    rw [right_coordinates, right_heading]
    exact (A.place_start k.succ r).symm)
  rw [left_bank, right_bank]
  exact MetricGluing.point_eq_of_glue A.Cell ⟨k, r, rfl, rfl⟩

theorem faceMap_eq_of_same_heading (i j : Fin (n + 1))
    (x : A.Cell i) (y : A.Cell j) (r : ℝ≥0) (θ : ℝ)
    (left_bounds : θ ∈ Set.Icc (A.heading i.castSucc) (A.heading i.succ))
    (right_bounds : θ ∈ Set.Icc (A.heading j.castSucc) (A.heading j.succ))
    (left_coordinates : A.place i x = (r : ℂ) * polarRay θ)
    (right_coordinates : A.place j y = (r : ℂ) * polarRay θ) :
    A.faceMap i x = A.faceMap j y := by
  rcases lt_trichotomy i j with ordered | same | ordered
  · exact A.faceMap_eq_of_same_heading_of_lt i j ordered x y r θ
      left_bounds right_bounds left_coordinates right_coordinates
  · subst j
    exact congrArg (A.faceMap i)
      ((A.place_isometry i).injective (left_coordinates.trans right_coordinates.symm))
  · exact (A.faceMap_eq_of_same_heading_of_lt j i ordered y x r θ
      right_bounds left_bounds right_coordinates left_coordinates).symm

theorem faceMap_eq_initial_bank (i : Fin (n + 1)) (x : A.Cell i) (r : ℝ≥0)
    (bounds : 0 ∈ Set.Icc (A.heading i.castSucc) (A.heading i.succ))
    (coordinates : A.place i x = (r : ℂ) * polarRay 0) :
    A.faceMap i x = A.faceMap 0 (A.start 0 r) := by
  apply A.faceMap_eq_of_same_heading i 0 x (A.start 0 r) r 0 bounds
  · exact ⟨A.heading_zero.le, A.heading_nonneg _⟩
  · exact coordinates
  · have zero : A.heading (0 : Fin (n + 1)).castSucc = 0 := A.heading_zero
    simpa only [zero] using A.place_start (0 : Fin (n + 1)) r

theorem faceMap_eq_terminal_bank (i : Fin (n + 1)) (x : A.Cell i) (r : ℝ≥0)
    (bounds : A.totalAngle ∈ Set.Icc (A.heading i.castSucc) (A.heading i.succ))
    (coordinates : A.place i x = (r : ℂ) * polarRay A.totalAngle) :
    A.faceMap i x = A.faceMap (Fin.last n) (A.finish (Fin.last n) r) := by
  apply A.faceMap_eq_of_same_heading i (Fin.last n) x (A.finish (Fin.last n) r)
    r A.totalAngle bounds
  · refine ⟨A.heading_le_totalAngle _, ?_⟩
    rw [Fin.succ_last, A.heading_last]
  · exact coordinates
  · simpa only [Fin.succ_last, A.heading_last] using A.place_finish (Fin.last n) r

/-- At one full turn, the only extra planar coincidences are the two outer banks. -/
theorem develop_fiber_cases (full : A.totalAngle = 2 * Real.pi) (z w : A.Surface)
    (equal : A.develop z = A.develop w) :
    z = w ∨ ∃ r : ℝ≥0,
      (z = A.faceMap 0 (A.start 0 r) ∧ w = A.faceMap (Fin.last n) (A.finish (Fin.last n) r)) ∨
      (z = A.faceMap (Fin.last n) (A.finish (Fin.last n) r) ∧ w = A.faceMap 0 (A.start 0 r)) := by
  obtain ⟨⟨i, x⟩, rfl⟩ := MetricGluing.point_surjective A.Cell A.glue z
  obtain ⟨⟨j, y⟩, rfl⟩ := MetricGluing.point_surjective A.Cell A.glue w
  change A.place i x = A.place j y at equal
  by_cases zero : A.place i x = 0
  · exact Or.inl ((A.faceMap_eq_origin_of_place_zero i x zero).trans
      (A.faceMap_eq_origin_of_place_zero j y (equal.symm.trans zero)).symm)
  · obtain ⟨r, θ, θbounds, θpoint⟩ := A.exists_place_polar i x
    obtain ⟨s, φ, φbounds, φpoint⟩ := A.exists_place_polar j y
    have radii : r = s := polar_radius_eq r s θ φ (θpoint.symm.trans (equal.trans φpoint))
    subst s
    have nonzero : r ≠ 0 := by
      intro radius_zero
      apply zero
      rw [θpoint, radius_zero]
      simp
    have θglobal : θ ∈ Set.Icc 0 (2 * Real.pi) := by
      rw [← full]
      exact ⟨(A.heading_nonneg _).trans θbounds.1,
        θbounds.2.trans (A.heading_le_totalAngle _)⟩
    have φglobal : φ ∈ Set.Icc 0 (2 * Real.pi) := by
      rw [← full]
      exact ⟨(A.heading_nonneg _).trans φbounds.1,
        φbounds.2.trans (A.heading_le_totalAngle _)⟩
    rcases polar_eq_heading_cases r nonzero θ φ θglobal φglobal
        (θpoint.symm.trans (equal.trans φpoint)) with same | ⟨first, last⟩ | ⟨last, first⟩
    · rw [← same] at φbounds φpoint
      exact Or.inl (A.faceMap_eq_of_same_heading i j x y r θ
        θbounds φbounds θpoint φpoint)
    · have terminal : φ = A.totalAngle := last.trans full.symm
      refine Or.inr ⟨r, Or.inl ⟨?_, ?_⟩⟩
      · exact A.faceMap_eq_initial_bank i x r
          (by simpa only [first] using θbounds) (by simpa only [first] using θpoint)
      · exact A.faceMap_eq_terminal_bank j y r
          (by simpa only [terminal] using φbounds) (by simpa only [terminal] using φpoint)
    · have terminal : θ = A.totalAngle := last.trans full.symm
      refine Or.inr ⟨r, Or.inr ⟨?_, ?_⟩⟩
      · exact A.faceMap_eq_terminal_bank i x r
          (by simpa only [terminal] using θbounds) (by simpa only [terminal] using θpoint)
      · exact A.faceMap_eq_initial_bank j y r
          (by simpa only [first] using φbounds) (by simpa only [first] using φpoint)

end Unfoldings.AngularFan
