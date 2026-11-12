module

public import Unfoldings.Cap.EmptyCircleContinuation
public import Unfoldings.Cap.GeometricFreshWaterfallLeaf
public import Unfoldings.Geometry.SubdivisionCollapsedBanks
public import Unfoldings.Geometry.SubdivisionNonemptyCells

/-! Some actual waterfall strip survives on each controlled source circle. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))

theorem exists_waterfall_closed_circle_survivor (i : FiveSector) {ε cutoff physicalRadius
  radius : ℝ}
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (traces : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      N.RadialStripTraceData positive small D
        (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i cell.val ε cutoff)
    (cutoff_positive : 0 < cutoff)
    (continuations : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      (traces cell).value '' closure (cell.val.openSlab 0 cutoff) ∩
          {z | ‖z - (traces cell).center‖ = radius} = ∅ →
        (cell.val.openSlab 0 cutoff).Nonempty →
          Nonempty (B.EmptyCircleContinuation i (traces cell) physicalRadius radius)) :
    ∃ cell : {S : MonotoneStrip // S ∈ P.cells},
      ((traces cell).value '' closure (cell.val.openSlab 0 cutoff) ∩
        {z | ‖z - (traces cell).center‖ = radius}).Nonempty := by
  by_contra absent
  push Not at absent
  have collapsed := P.banks_eq_of_all_cells_collapsed cutoff (fun S member => by
    let cell : {S : MonotoneStrip // S ∈ P.cells} := ⟨S, member⟩
    by_cases physical : (S.openSlab 0 cutoff).Nonempty
    · obtain ⟨terminal⟩ := continuations cell
        (absent cell) physical
      exact terminal.merged cutoff ⟨terminal.height_bounds.2.le, le_rfl⟩
    · have empty : S.openSlab 0 cutoff = ∅ := Set.not_nonempty_iff_eq_empty.mp physical
      exact congrArg Complex.re (S.banks_point_eqOn_of_empty_openSlab cutoff_positive empty
        ⟨cutoff_positive.le, le_rfl⟩))
  exact ((fiveSectorFrame t positive small i).enclosingStrip_width_pos
    (fiveSector_banks_orient_pos positive small i) cutoff_positive).ne collapsed

open Classical in
theorem waterfall_closed_circle_survivors_ne_nil (i : FiveSector) {ε cutoff physicalRadius
  radius : ℝ}
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (traces : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      N.RadialStripTraceData positive small D
        (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i cell.val ε cutoff)
    (cutoff_positive : 0 < cutoff)
    (continuations : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      (traces cell).value '' closure (cell.val.openSlab 0 cutoff) ∩
          {z | ‖z - (traces cell).center‖ = radius} = ∅ →
        (cell.val.openSlab 0 cutoff).Nonempty →
          Nonempty (B.EmptyCircleContinuation i (traces cell) physicalRadius radius)) :
    (P.nonemptyCells cutoff |>.filter (fun cell => decide
      ((traces cell).value '' closure (cell.val.openSlab 0 cutoff) ∩
        {z | ‖z - (traces cell).center‖ = radius}).Nonempty)) ≠ [] := by
  obtain ⟨cell, meets⟩ :=
    B.exists_waterfall_closed_circle_survivor i P traces cutoff_positive continuations
  have physical : (cell.val.openSlab 0 cutoff).Nonempty := by
    obtain ⟨_, ⟨p, member, _⟩, _⟩ := meets
    exact closure_nonempty_iff.mp ⟨p, member⟩
  apply List.ne_nil_of_mem (a := cell)
  exact List.mem_filter.mpr ⟨(P.mem_nonemptyCells cutoff cell).mpr physical,
    by simpa only [decide_eq_true_eq] using meets⟩

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
