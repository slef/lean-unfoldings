module

public import Unfoldings.Cap.TerminalRecordStep
public import Unfoldings.Cap.RegularCircleRadius
public import Unfoldings.Cap.RadialStripCircleWidth
public import Unfoldings.Geometry.StripBankContacts
public import Unfoldings.Topology.FiniteRecordProgress

/-! Early circle crossings beyond a terminated prefix are controlled by the first later terminal. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {i : FiveSector}

variable
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    (leaf_vertices : ∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (footprint : Q.footprint = K.clipFootprint Z) {cutoff : ℝ}
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision) {ε : ℝ}
    (traces : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      R.RadialStripTraceData positive small D
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i cell.val ε cutoff)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (budget : FineC.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (nonnegative : 0 ≤ ε) (small_error : ε ≤ 1 / 2)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement Q
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference)
        (fiveSectorFrame t positive small i).place f).linear z - z‖ ≤ ε * ‖z‖)
    (pinches : ∀ cell : {S : MonotoneStrip // S ∈ P.cells}, cell.val.ApproachedPinchesIn
      (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
          M.extendedGeometricCuts F} =>
        (fiveSectorFrame t positive small i).place
          (Q.projectedVertex v.val - K.projectedVertex origin))) 0 cutoff)

variable {n : ℕ} (cells : Fin (n + 1) → {S : MonotoneStrip // S ∈ P.cells})
  (contacts : ∀ j : Fin n, Set.EqOn (cells j.castSucc).val.upper.point
    (cells j.succ).val.lower.point (Set.Icc 0 cutoff))
  {physicalRadius radius : ℝ}
  (terminals : ∀ j, B.EmptyCircleContinuation i (traces (cells j)) physicalRadius radius)
  (tails : ∀ j, (cells j).val.TerminalTailsFrom
    (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
    (fun leaf => leaf.tailGraph.graph) cutoff)
  (source : {S : MonotoneStrip // S ∈ P.cells})
  (slice : source.val.BankCircleSlice (traces source).value (traces source).center cutoff radius)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)

include outward leaf_vertices footprint deep curvature_covered budget nonnegative
  small_error linear_error pinches contacts tails radius_positive far

/-- All cells before the first tall-enough terminal have already merged.
The approached later bank follows their actual tail from the tested height. -/
theorem upper_circle_re_le_after_terminal_prefix_of_contacts (j : Fin (n + 1))
    (nonzero : (0 : Fin (n + 1)) < j)
    (ordered : List.Sublist [source, cells j] P.cells.attach)
    (before_terminal : slice.upperHeight ≤ (terminals j).height)
    (earlier : ∀ k : Fin (n + 1), k < j → (terminals k).height < slice.upperHeight) :
    ((traces source).value (source.val.upper.point slice.upperHeight)).re ≤
      ((traces (cells j)).value ((cells j).val.lower.point (terminals j).height)).re := by
  have height := ((traces source).circle_slice_heights radius_positive far slice).2
  have included : (cells j).val.openSlab 0 cutoff ⊆ (traces (cells j)).strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have endpoint := closure_mono included (terminals j).lower_closed
  have at_height := (traces (cells j)).lower_bank_closed_before endpoint
    (by rw [(cells j).val.lower.point_height]; exact ⟨height.1.le, before_terminal⟩)
  have gap := waterfall_closed_level_bank_order R outward D B leaf_vertices footprint deep P traces
    curvature_covered budget nonnegative small_error linear_error pinches source (cells j) ordered
    height slice.upper_closed at_height
  have agreement : Set.EqOn (cells j).val.lower.point (cells 0).val.lower.point
      (Set.Icc slice.upperHeight (terminals j).height) := by
    intro h member
    have coordinates := MonotoneStrip.lower_coordinates_eq_between_of_contacts
      (fun k => (cells k).val) (fun k => congrArg Complex.re
        (contacts k ⟨height.1.le.trans member.1,
          member.2.trans (terminals j).height_bounds.2.le⟩)) 0 j (Nat.zero_le _) (fun k _ before =>
        (terminals k).merged h ⟨(earlier k before).le.trans member.1,
          member.2.trans (terminals j).height_bounds.2.le⟩)
    exact (cells j).val.lower.point_eq_of_same_coordinate (cells 0).val.lower coordinates.symm
  have progress := terminal_tail_bank_interval_order_from_height R D B (traces (cells 0))
    (tails 0) (terminals 0) (traces (cells j)) (Or.inl rfl) deep (earlier 0 nonzero).le
    before_terminal (terminals j).height_bounds.2.le agreement endpoint
  exact gap.1.trans progress.1

/-- The analogous argument from the right uses the upper bank of the first
tall-enough terminal, retaining all terminal copies and endpoint heights. -/
theorem lower_circle_im_le_before_terminal_suffix_of_contacts (j : Fin (n + 1))
    (nonlast : j < Fin.last n)
    (ordered : List.Sublist [cells j, source] P.cells.attach)
    (before_terminal : slice.lowerHeight ≤ (terminals j).height)
    (later : ∀ k : Fin (n + 1), j < k → (terminals k).height < slice.lowerHeight) :
    ((traces source).value (source.val.lower.point slice.lowerHeight)).im ≤
      ((traces (cells j)).value ((cells j).val.lower.point (terminals j).height)).im := by
  have height := ((traces source).circle_slice_heights radius_positive far slice).1
  have included : (cells j).val.openSlab 0 cutoff ⊆ (traces (cells j)).strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have endpoint := closure_mono included (terminals j).upper_closed
  have at_height := (traces (cells j)).upper_bank_closed_before endpoint
    (by rw [(cells j).val.upper.point_height]; exact ⟨height.1.le, before_terminal⟩)
  have gap := waterfall_closed_level_bank_order R outward D B leaf_vertices footprint deep P traces
    curvature_covered budget nonnegative small_error linear_error pinches (cells j) source ordered
    height at_height slice.lower_closed
  have agreement : Set.EqOn (cells j).val.upper.point (cells (Fin.last n)).val.lower.point
      (Set.Icc slice.lowerHeight (terminals j).height) := by
    intro h member
    have coordinates := MonotoneStrip.upper_coordinates_eq_between_of_contacts
      (fun k => (cells k).val) (fun k => congrArg Complex.re
        (contacts k ⟨height.1.le.trans member.1,
          member.2.trans (terminals j).height_bounds.2.le⟩)) j (Fin.last n) nonlast.le
      (fun k after_j _ =>
        (terminals k).merged h ⟨(later k after_j).le.trans member.1,
          member.2.trans (terminals j).height_bounds.2.le⟩)
    have source_collapsed := (terminals (Fin.last n)).merged h
      ⟨(later (Fin.last n) nonlast).le.trans member.1,
        member.2.trans (terminals j).height_bounds.2.le⟩
    exact (cells j).val.upper.point_eq_of_same_coordinate (cells (Fin.last n)).val.lower
      (coordinates.trans source_collapsed.symm)
  have progress := terminal_tail_bank_interval_order_from_height R D B
    (traces (cells (Fin.last n))) (tails (Fin.last n)) (terminals (Fin.last n))
    (traces (cells j)) (Or.inr rfl) deep (later (Fin.last n) nonlast).le
    before_terminal (terminals j).height_bounds.2.le agreement endpoint
  have terminal_equal := (cells j).val.lower.point_eq_of_same_coordinate (cells j).val.upper
    ((terminals j).merged (terminals j).height ⟨le_rfl, (terminals j).height_bounds.2.le⟩)
  rw [← terminal_equal] at progress
  exact gap.2.trans progress.2

end Unfoldings.ConvexCap.SectorForest
