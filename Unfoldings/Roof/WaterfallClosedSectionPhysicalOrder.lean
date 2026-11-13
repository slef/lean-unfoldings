module

public import Unfoldings.Roof.WaterfallClosedSectionOrder
public import Unfoldings.Roof.ClosedSectionRemovedRunContact
public import Unfoldings.Cap.ClosedCircleSectionLexOrder

/-! Full survivor order retains physical point equality whenever developed bank values coincide. -/

@[expose] public section

noncomputable section


namespace Unfoldings.ConvexRoof.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outerDomain : Set Plane} {F : K.SkirtTailFamily outerDomain (origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {i : FiveSector}

variable
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    (leaf_vertices : ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (footprint : Q.footprint = outerDomain) {cutoff : ℝ}
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision) {ε : ℝ}
    (traces : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      R.RadialStripTraceData positive small D
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i cell.val ε cutoff)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (budget : FineC.totalInteriorAngularDefect Set.univ < Real.pi)
    (nonnegative : 0 ≤ ε) (small_error : ε < 1 / 2)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement Q
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference)
        (fiveSectorFrame t positive small i).place f).linear z - z‖ ≤ ε * ‖z‖)
    (pinches : ∀ cell : {S : MonotoneStrip // S ∈ P.cells}, cell.val.ApproachedPinchesIn
      (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
          M.extendedGeometricCuts F} =>
        (fiveSectorFrame t positive small i).place
          (Q.projectedVertex v.val - origin))) 0 cutoff)

variable
  (provenance : ∀ H ∈ P.separators,
    ∃ leaf : M.GeometricSectorLeaf F covered positive small i,
      leaf.point.re + leaf.point.im ≤ cutoff ∧
        MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
  (represented : ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
    leaf.point.re + leaf.point.im ≤ cutoff → ∃ H ∈ P.separators,
      MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
  (leaf_coherent : ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
    D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))

variable {physicalRadius radius : ℝ}

variable {μ : ℝ} (numerical : ε * (1 + ε) < μ - ε)
  (margins : ∀ cell : {S : MonotoneStrip // S ∈ P.cells}, ∀ z ∈ cell.val.carrier,
    0 ≤ z.re + z.im → μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)


variable (all_tails : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
    cell.val.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
  (continuations : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
    (traces cell).value '' closure (cell.val.openSlab 0 cutoff) ∩
        {z | ‖z - (traces cell).center‖ = radius} = ∅ →
      (cell.val.openSlab 0 cutoff).Nonempty →
        Nonempty (B.EmptyCircleContinuation i (traces cell) physicalRadius radius))
  (regular_continuations : ∀ r ∈ Set.Ioo 0 radius,
    ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      r ∉ (traces cell).emptyCircleExceptions →
      (traces cell).value '' cell.val.openSlab 0 cutoff ∩
          {z | ‖z - (traces cell).center‖ = r} = ∅ →
      (cell.val.openSlab 0 cutoff).Nonempty →
        Nonempty (B.EmptyCircleContinuation i (traces cell) physicalRadius r))
  (enclosing_margin : ∀ z ∈ (fiveSectorFrame t positive small i).enclosingStrip.carrier,
    0 ≤ z.re + z.im → μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)


include outward leaf_vertices footprint deep curvature_covered budget nonnegative
  small_error linear_error pinches provenance represented leaf_coherent numerical margins
  radius_positive far all_tails continuations regular_continuations enclosing_margin

open Classical in
/-- Removing empty physical cells and disappearing circle runs preserves the
actual order of every surviving pair of bank endpoints. The slices may be
chosen independently by the caller; radial uniqueness makes their choices immaterial. -/
theorem waterfall_closed_section_physical_contacts
    (slices : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      ((traces cell).value '' closure (cell.val.openSlab 0 cutoff) ∩
        {z | ‖z - (traces cell).center‖ = radius}).Nonempty →
      cell.val.ClosedBankCircleSection (traces cell).value (traces cell).center cutoff radius) :
    ((P.nonemptyCells cutoff).filter (fun cell => decide
      ((traces cell).value '' closure (cell.val.openSlab 0 cutoff) ∩
        {z | ‖z - (traces cell).center‖ = radius}).Nonempty)).Pairwise
      (fun a b => ∀ meet_a meet_b,
        (traces a).value (a.val.upper.point (slices a meet_a).upperHeight) =
          (traces b).value (b.val.lower.point (slices b meet_b).lowerHeight) →
        a.val.upper.point (slices a meet_a).upperHeight =
          b.val.lower.point (slices b meet_b).lowerHeight) := by
  classical
  let meets := fun cell : {S : MonotoneStrip // S ∈ P.cells} =>
    ((traces cell).value '' closure (cell.val.openSlab 0 cutoff) ∩
      {z | ‖z - (traces cell).center‖ = radius}).Nonempty
  let keep := fun cell => decide (meets cell)
  let survivors := (P.nonemptyCells cutoff).filter keep
  have close_margin : ε < μ := by nlinarith [sq_nonneg ε]
  let first : {S : MonotoneStrip // S ∈ P.cells} → ℝ ×ₗ Set ℂ := fun cell =>
    if meet : meets cell then
      let z := (traces cell).value (cell.val.lower.point (slices cell meet).lowerHeight) -
        (traces cell).center
      toLex (z.re, {cell.val.lower.point (slices cell meet).lowerHeight}) else toLex (0, ∅)
  let last : {S : MonotoneStrip // S ∈ P.cells} → ℝ ×ₗ Set ℂ := fun cell =>
    if meet : meets cell then
      let z := (traces cell).value (cell.val.upper.point (slices cell meet).upperHeight) -
        (traces cell).center
      toLex (z.re, {cell.val.upper.point (slices cell meet).upperHeight}) else toLex (0, ∅)
  have survivor_meets {cell} (member : cell ∈ survivors) : meets cell :=
    of_decide_eq_true (List.mem_filter.mp member).2
  have within : ∀ cell ∈ survivors, first cell ≤ last cell := by
    intro cell member
    have meet := survivor_meets member
    simp only [first, last, dite_eq_left meet]
    exact (traces cell).closed_circle_section_lex_order (slices cell meet) nonnegative
      small_error numerical linear_error (margins cell) radius_positive far
  have cutoff_positive : 0 < cutoff := by
    by_contra nonpositive
    have bound := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr small_error.le)
      (not_lt.mp nonpositive)
    exact (not_lt_of_ge bound) (radius_positive.trans far)
  have chain : survivors.IsChain (fun a b => last a ≤ first b) := by
    apply isChain_filter_of_removed_runs keep (P.nonemptyCells cutoff)
    intro before a middle b after equal kept_a kept_b removed
    have meet_a : meets a := of_decide_eq_true kept_a
    have meet_b : meets b := of_decide_eq_true kept_b
    have run : List.IsInfix (a :: (middle ++ [b])) (P.nonemptyCells cutoff) := by
      refine ⟨before, after, ?_⟩
      rw [equal]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    have order := waterfall_closed_section_facing_bank_order R outward D B leaf_vertices
      footprint deep P traces curvature_covered budget nonnegative small_error linear_error pinches
      provenance represented leaf_coherent numerical margins radius_positive far all_tails
      regular_continuations a b
      (by
        have subset : List.Sublist [a, b] (a :: (middle ++ [b])) := by
          simp
        exact subset.trans (run.sublist.trans (P.nonemptyCells_sublist cutoff)))
      (slices a meet_a) (slices b meet_b)
    simp only [first, last, dite_eq_left meet_a, dite_eq_left meet_b]
    apply Prod.Lex.toLex_le_toLex'.mpr
    refine ⟨order, ?_⟩
    intro coordinate_equal
    have first_quadrant := (traces a).strict_quadrant_of_closed_margin close_margin (margins a)
      (slices a meet_a).upper_closed
      ((traces a).closed_height_pos_of_norm (slices a meet_a).upper_closed
        (by rw [(slices a meet_a).upper_radius]; exact radius_positive))
    have last_quadrant := (traces b).strict_quadrant_of_closed_margin close_margin (margins b)
      (slices b meet_b).lower_closed
      ((traces b).closed_height_pos_of_norm (slices b meet_b).lower_closed
        (by rw [(slices b meet_b).lower_radius]; exact radius_positive))
    have centered_equal := complex_eq_of_norm_re_eq
      ((slices a meet_a).upper_radius.trans (slices b meet_b).lower_radius.symm)
      coordinate_equal first_quadrant.2.le last_quadrant.2.le
    have same_values : (traces a).value (a.val.upper.point (slices a meet_a).upperHeight) =
        (traces b).value (b.val.lower.point (slices b meet_b).lowerHeight) :=
      sub_left_inj.mp centered_equal
    have physical := closed_section_contact_across_removed_run_same_point R outward D B
      leaf_vertices
      footprint
      deep P traces curvature_covered budget nonnegative small_error linear_error pinches
      provenance represented leaf_coherent a b (slices a meet_a) (slices b meet_b)
      numerical (margins a) (margins b) radius_positive far all_tails continuations
      regular_continuations enclosing_margin middle
      (run.sublist.trans (P.nonemptyCells_sublist cutoff))
      ((P.nonemptyCells_bank_contact_chain cutoff_positive).infix run)
      (fun cell member => (P.mem_nonemptyCells cutoff cell).mp
        (run.subset (List.mem_cons_of_mem _ (List.mem_append_left _ member))))
      (fun cell member => Set.not_nonempty_iff_eq_empty.mp (by
        intro meet
        exact removed cell member (by simpa only [keep, decide_eq_true_eq] using meet))) same_values
    exact Set.singleton_subset_singleton.mpr
      ((fiveSectorFrame t positive small i).place.symm.injective physical)
  have ordered := ordered_bank_pieces_pairwise first last survivors within chain
  apply List.Pairwise.imp_of_mem _ ordered
  intro a b _ _ gap meet_a meet_b same_values
  have present_a : meets a := meet_a
  have present_b : meets b := meet_b
  simp only [first, last, dite_eq_left present_a, dite_eq_left present_b] at gap
  have certified := Prod.Lex.toLex_le_toLex'.mp gap
  have coordinates := congrArg (fun z : ℂ => (z - (traces a).center).re) same_values
  exact Set.singleton_subset_singleton.mp (certified.2 coordinates)

end Unfoldings.ConvexRoof.SectorForest
