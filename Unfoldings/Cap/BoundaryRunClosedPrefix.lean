module

public import Unfoldings.Cap.BoundaryRunTerminalPoint
public import Unfoldings.Cap.RadialStripClosedBanks
public import Unfoldings.Topology.FiniteMaxPositions
public import Unfoldings.Geometry.StripSlabApproach

/-! Every boundary-prefix position is approached by an actual disappearing-run strip. -/

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
  (pivot : Fin (n + 1))

include contacts

theorem first_run_approached_boundary_prefix {h : ℝ} (positive_height : 0 < h)
    (before : h ≤ (terminals pivot).height)
    (outer : Set.EqOn (fiveSectorFrame t positive small i).enclosingStrip.lower.point
      (cells 0).lower.point (Set.Icc 0 cutoff)) :
    ∃ k : Fin (n + 1),
      (fiveSectorFrame t positive small i).enclosingStrip.lower.point h = (cells k).lower.point h ∧
      (cells k).lower.point h ∈ closure ((cells k).openSlab 0 cutoff) := by
  obtain ⟨k, _, reaches, earlier⟩ := exists_first_ge_position
    (fun j => (terminals j).height) h pivot before
  have height : h ∈ Set.Ioo 0 cutoff :=
    ⟨positive_height, reaches.trans_lt (terminals k).height_bounds.2⟩
  have coordinates := MonotoneStrip.lower_coordinates_eq_between_of_contacts cells
    (fun j => congrArg Complex.re (contacts j ⟨height.1.le, height.2.le⟩))
    0 k (Nat.zero_le _) (fun j _ before_k => (terminals j).merged h
      ⟨(earlier j before_k).le, height.2.le⟩)
  have contact := (outer ⟨height.1.le, height.2.le⟩).trans
    ((cells 0).lower.point_eq_of_same_coordinate (cells k).lower coordinates)
  have included : (cells k).openSlab 0 cutoff ⊆ (traces k).strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have endpoint := closure_mono included (terminals k).lower_closed
  have closed := (traces k).lower_bank_closed_before endpoint
    (by rw [(cells k).lower.point_height]; exact ⟨height.1.le, reaches⟩)
  exact ⟨k, contact, (cells k).mem_closure_openSlab_of_height closed
    (by rw [(cells k).lower.point_height]; exact height)⟩

theorem last_run_approached_boundary_prefix {h : ℝ} (positive_height : 0 < h)
    (before : h ≤ (terminals pivot).height)
    (outer : Set.EqOn (cells (Fin.last n)).upper.point
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff)) :
    ∃ k : Fin (n + 1),
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point h = (cells k).upper.point h ∧
      (cells k).upper.point h ∈ closure ((cells k).openSlab 0 cutoff) := by
  obtain ⟨k, _, reaches, later⟩ := exists_last_ge_position
    (fun j => (terminals j).height) h pivot before
  have height : h ∈ Set.Ioo 0 cutoff :=
    ⟨positive_height, reaches.trans_lt (terminals k).height_bounds.2⟩
  have coordinates := MonotoneStrip.upper_coordinates_eq_between_of_contacts cells
    (fun j => congrArg Complex.re (contacts j ⟨height.1.le, height.2.le⟩))
    k (Fin.last n) (Fin.le_last _) (fun j after_k _ => (terminals j).merged h
      ⟨(later j after_k).le, height.2.le⟩)
  have contact := ((cells k).upper.point_eq_of_same_coordinate
    (cells (Fin.last n)).upper coordinates).trans (outer ⟨height.1.le, height.2.le⟩)
  have included : (cells k).openSlab 0 cutoff ⊆ (traces k).strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have endpoint := closure_mono included (terminals k).upper_closed
  have closed := (traces k).upper_bank_closed_before endpoint
    (by rw [(cells k).upper.point_height]; exact ⟨height.1.le, reaches⟩)
  exact ⟨k, contact.symm, (cells k).mem_closure_openSlab_of_height closed
    (by rw [(cells k).upper.point_height]; exact height)⟩

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
