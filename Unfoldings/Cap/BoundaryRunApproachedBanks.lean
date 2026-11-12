module

public import Unfoldings.Cap.BoundaryRunTerminalPoint
public import Mathlib.Data.Fintype.Lattice

/-! Extreme maximal terminals approach their actual enclosing bank from below. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

private theorem exists_threshold_below {ι : Type*} [Finite ι] [Nonempty ι]
    (height : ι → ℝ) (keep : ι → Prop) {top : ℝ} (positive : 0 < top)
    (below : ∀ j, keep j → height j < top) :
    ∃ a ∈ Set.Ioo (0 : ℝ) top, ∀ j, keep j → height j < a := by
  classical
  let selected := fun j => if keep j then max 0 (height j) else 0
  obtain ⟨j, maximal⟩ := Finite.exists_max selected
  have nonnegative : 0 ≤ selected j := by
    dsimp only [selected]
    split_ifs <;> positivity
  have bound : selected j < top := by
    dsimp only [selected]
    split_ifs with member
    · exact max_lt positive (below j member)
    · exact positive
  refine ⟨(selected j + top) / 2, ⟨by linarith, by linarith⟩, ?_⟩
  intro k member
  have lower : height k ≤ selected k := by
    dsimp only [selected]
    rw [ite_eq_left member]
    exact le_max_right _ _
  have upper := maximal k
  linarith

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))
  (i : FiveSector) {ε cutoff physicalRadius radius : ℝ} {n : ℕ}
  (cells : Fin (n + 1) → MonotoneStrip)
  (traces : ∀ j, N.RadialStripTraceData positive small D
    (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i (cells j) ε cutoff)
  (contacts : ∀ j : Fin n, Set.EqOn (cells j.castSucc).upper.point
    (cells j.succ).lower.point (Set.Icc 0 cutoff))
  (terminals : ∀ j, B.EmptyCircleContinuation i (traces j) physicalRadius radius)
  (pivot : Fin (n + 1))

include contacts

/-- Choosing the first maximal terminal is essential: earlier tied terminals
would prevent contact with the lower enclosing bank at heights just below it. -/
theorem first_run_maximum_approaches_lower_bank
    (strict_before : ∀ j, j < pivot → (terminals j).height < (terminals pivot).height)
    (outer : Set.EqOn (fiveSectorFrame t positive small i).enclosingStrip.lower.point
      (cells 0).lower.point (Set.Icc 0 cutoff)) :
    ∃ a ∈ Set.Ioo (0 : ℝ) (terminals pivot).height,
      Set.EqOn (fiveSectorFrame t positive small i).enclosingStrip.lower.point
        (cells pivot).lower.point (Set.Icc a (terminals pivot).height) := by
  obtain ⟨a, bounds, threshold⟩ := exists_threshold_below
    (fun j => (terminals j).height) (fun j => j < pivot)
    (terminals pivot).height_bounds.1 strict_before
  refine ⟨a, bounds, ?_⟩
  intro h member
  have height : h ∈ Set.Icc 0 cutoff :=
    ⟨bounds.1.le.trans member.1, member.2.trans (terminals pivot).height_bounds.2.le⟩
  have equal := MonotoneStrip.lower_coordinates_eq_between_of_contacts cells
    (fun j => congrArg Complex.re (contacts j height)) 0 pivot (Nat.zero_le _)
    (fun j _ earlier => (terminals j).merged h
      ⟨(threshold j earlier).le.trans member.1, height.2⟩)
  exact (outer height).trans ((cells 0).lower.point_eq_of_same_coordinate
    (cells pivot).lower equal)

/-- The last maximal terminal retains its own approached upper bank. Its
collapsed continuation may merge later, but no later trace value is used. -/
theorem last_run_maximum_approaches_upper_bank
    (strict_after : ∀ j, pivot < j → (terminals j).height < (terminals pivot).height)
    (outer : Set.EqOn (cells (Fin.last n)).upper.point
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff)) :
    ∃ a ∈ Set.Ioo (0 : ℝ) (terminals pivot).height,
      Set.EqOn (cells pivot).upper.point
        (fiveSectorFrame t positive small i).enclosingStrip.upper.point
          (Set.Icc a (terminals pivot).height) := by
  obtain ⟨a, bounds, threshold⟩ := exists_threshold_below
    (fun j => (terminals j).height) (fun j => pivot < j)
    (terminals pivot).height_bounds.1 strict_after
  refine ⟨a, bounds, ?_⟩
  intro h member
  have height : h ∈ Set.Icc 0 cutoff :=
    ⟨bounds.1.le.trans member.1, member.2.trans (terminals pivot).height_bounds.2.le⟩
  have equal := MonotoneStrip.upper_coordinates_eq_between_of_contacts cells
    (fun j => congrArg Complex.re (contacts j height)) pivot (Fin.last n) (Fin.le_last _)
    (fun j later _ => (terminals j).merged h
      ⟨(threshold j later).le.trans member.1, height.2⟩)
  exact ((cells pivot).upper.point_eq_of_same_coordinate
    (cells (Fin.last n)).upper equal).trans (outer height)

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
