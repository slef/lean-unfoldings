module

public import Unfoldings.Cap.EmptyCircleContinuation
public import Unfoldings.Cap.SectorBoundaryCutPoints
public import Unfoldings.Geometry.StripBankContacts

/-! Extreme disappearing runs have an actual maximal terminal on the enclosing sector ray. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

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
  (pivot : Fin (n + 1)) (highest : ∀ j, (terminals j).height ≤ (terminals pivot).height)

include contacts highest

theorem first_run_lower_tail_on_boundary
    (outer : Set.EqOn (fiveSectorFrame t positive small i).enclosingStrip.lower.point
      (cells 0).lower.point (Set.Icc 0 cutoff)) :
    Set.EqOn (fiveSectorFrame t positive small i).enclosingStrip.lower.point
      (cells pivot).lower.point (Set.Icc (terminals pivot).height cutoff) := by
  intro h member
  have height : h ∈ Set.Icc 0 cutoff :=
    ⟨(terminals pivot).height_bounds.1.le.trans member.1, member.2⟩
  have equal := MonotoneStrip.lower_coordinates_eq_between_of_contacts cells
    (fun j => congrArg Complex.re (contacts j height)) 0 pivot (Nat.zero_le _)
    (fun j _ _ => (terminals j).merged h ⟨(highest j).trans member.1, member.2⟩)
  exact (outer height).trans ((cells 0).lower.point_eq_of_same_coordinate
    (cells pivot).lower equal)

theorem last_run_lower_tail_on_boundary
    (outer : Set.EqOn (cells (Fin.last n)).upper.point
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff)) :
    Set.EqOn (cells pivot).lower.point
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point
        (Set.Icc (terminals pivot).height cutoff) := by
  intro h member
  have height : h ∈ Set.Icc 0 cutoff :=
    ⟨(terminals pivot).height_bounds.1.le.trans member.1, member.2⟩
  have equal := MonotoneStrip.collapsed_chain_points_of_contacts cells
    (fun j => congrArg Complex.re (contacts j height))
    (fun j => (terminals j).merged h ⟨(highest j).trans member.1, member.2⟩) pivot (Fin.last n)
  exact equal.trans (outer height)

theorem first_run_maximum_on_lower_bank
    (outer : Set.EqOn (fiveSectorFrame t positive small i).enclosingStrip.lower.point
      (cells 0).lower.point (Set.Icc 0 cutoff)) :
    (fiveSectorFrame t positive small i).enclosingStrip.lower.point (terminals pivot).height =
      (cells pivot).lower.point (terminals pivot).height := by
  have height : (terminals pivot).height ∈ Set.Icc 0 cutoff :=
    ⟨(terminals pivot).height_bounds.1.le, (terminals pivot).height_bounds.2.le⟩
  have equal := MonotoneStrip.lower_coordinates_eq_between_of_contacts cells
    (fun j => congrArg Complex.re (contacts j height)) 0 pivot (Nat.zero_le _)
    (fun j _ _ => (terminals j).merged _ ⟨highest j, height.2⟩)
  exact (outer height).trans ((cells 0).lower.point_eq_of_same_coordinate
    (cells pivot).lower equal)

theorem last_run_maximum_on_upper_bank
    (outer : Set.EqOn (cells (Fin.last n)).upper.point
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff)) :
    (cells pivot).lower.point (terminals pivot).height =
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point (terminals pivot).height := by
  have height : (terminals pivot).height ∈ Set.Icc 0 cutoff :=
    ⟨(terminals pivot).height_bounds.1.le, (terminals pivot).height_bounds.2.le⟩
  have equal := MonotoneStrip.collapsed_chain_points_of_contacts cells
    (fun j => congrArg Complex.re (contacts j height))
    (fun j => (terminals j).merged _ ⟨highest j, height.2⟩) pivot (Fin.last n)
  exact equal.trans (outer height)

/-- This concerns the actual fine terminal vertex and every sector, so it
can be used with the geometric boundary-cut classification. -/
theorem first_run_maximum_vertex_on_boundary
    (outer : Set.EqOn (fiveSectorFrame t positive small i).enclosingStrip.lower.point
      (cells 0).lower.point (Set.Icc 0 cutoff)) :
    ∀ j, K.projectedVertex (terminals pivot).vertex - source ∉ strictFiveSector t j := by
  have equal := B.first_run_maximum_on_lower_bank i cells traces contacts terminals
    pivot highest outer
  have boundary := (fiveSector_enclosingStrip_bank_not_strict_any positive small i
    (terminals pivot).height_bounds.1.le).1
  intro j
  rw [← (terminals pivot).physical, add_sub_cancel_left, ← equal]
  exact boundary j

theorem last_run_maximum_vertex_on_boundary
    (outer : Set.EqOn (cells (Fin.last n)).upper.point
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff)) :
    ∀ j, K.projectedVertex (terminals pivot).vertex - source ∉ strictFiveSector t j := by
  have equal := B.last_run_maximum_on_upper_bank i cells traces contacts terminals
    pivot highest outer
  have boundary := (fiveSector_enclosingStrip_bank_not_strict_any positive small i
    (terminals pivot).height_bounds.1.le).2
  intro j
  rw [← (terminals pivot).physical, add_sub_cancel_left, equal]
  exact boundary j

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
