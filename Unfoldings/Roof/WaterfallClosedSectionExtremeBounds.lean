module

public import Unfoldings.Roof.WaterfallClosedSectionOrder
public import Unfoldings.Cap.ClosedCircleSectionBounds
public import Unfoldings.Topology.OrderedBankEndpoints
public import Unfoldings.Geometry.QuadrantCircleCoordinateOrder
public import Unfoldings.Cap.ClosedSectionBankOrderLimit
public import Unfoldings.Cap.ClosedCircleAbsenceBounds
public import Unfoldings.Topology.OrderedBankPieces
public import Unfoldings.Topology.FilterDisjoint

/-! Full waterfall bank order includes closed-only sections and all vertex radii. -/

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
  (continuations : ∀ r ∈ Set.Ioo 0 radius,
    ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      r ∉ (traces cell).emptyCircleExceptions →
      (traces cell).value '' cell.val.openSlab 0 cutoff ∩
          {z | ‖z - (traces cell).center‖ = r} = ∅ →
      (cell.val.openSlab 0 cutoff).Nonempty →
        Nonempty (B.EmptyCircleContinuation i (traces cell) physicalRadius r))


include outward leaf_vertices footprint deep curvature_covered budget nonnegative
  small_error linear_error pinches provenance represented leaf_coherent numerical margins
  radius_positive far all_tails continuations

open Classical in
/-- Closed section extremes bound every actual closed circle image, including pinches. -/
theorem waterfall_closed_section_images_extreme_bounds
    (sections : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      ((traces cell).value '' closure (cell.val.openSlab 0 cutoff) ∩
        {z | ‖z - (traces cell).center‖ = radius}).Nonempty →
      cell.val.ClosedBankCircleSection (traces cell).value (traces cell).center cutoff radius)
    (head endPiece : {S : MonotoneStrip // S ∈ P.cells})
    (head_meets : ((traces head).value '' closure (head.val.openSlab 0 cutoff) ∩
      {z | ‖z - (traces head).center‖ = radius}).Nonempty)
    (end_meets : ((traces endPiece).value '' closure (endPiece.val.openSlab 0 cutoff) ∩
      {z | ‖z - (traces endPiece).center‖ = radius}).Nonempty)
    (at_head : ((P.nonemptyCells cutoff).filter (fun cell => decide
      ((traces cell).value '' closure (cell.val.openSlab 0 cutoff) ∩
        {z | ‖z - (traces cell).center‖ = radius}).Nonempty)).head? = some head)
    (at_end : ((P.nonemptyCells cutoff).filter (fun cell => decide
      ((traces cell).value '' closure (cell.val.openSlab 0 cutoff) ∩
        {z | ‖z - (traces cell).center‖ = radius}).Nonempty)).getLast? = some endPiece) :
    ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      (traces cell).outputFrame.symm ''
        ((traces cell).value '' closure (cell.val.openSlab 0 cutoff) ∩
          {z | ‖z - (traces cell).center‖ = radius}) ⊆
      weakCircleUpperCap (B.sectorFrame i) (D.projectedMap Q (origin)) radius
          ((traces endPiece).value
            (endPiece.val.upper.point (sections endPiece end_meets).upperHeight) -
              (traces endPiece).center).re ∩
        weakCircleLowerCap (B.sectorFrame i) (D.projectedMap Q (origin)) radius
          ((traces head).value (head.val.lower.point (sections head head_meets).lowerHeight) -
            (traces head).center).im := by
  classical
  let meets := fun cell : {S : MonotoneStrip // S ∈ P.cells} =>
    ((traces cell).value '' closure (cell.val.openSlab 0 cutoff) ∩
      {z | ‖z - (traces cell).center‖ = radius}).Nonempty
  let survivors := (P.nonemptyCells cutoff).filter (fun cell => decide (meets cell))
  let firstBank := fun cell => if meet : meets cell then
    ((traces cell).value (cell.val.lower.point (sections cell meet).lowerHeight) -
      (traces cell).center).re else 0
  let lastBank := fun cell => if meet : meets cell then
    ((traces cell).value (cell.val.upper.point (sections cell meet).upperHeight) -
      (traces cell).center).re else 0
  have survivor_meets {cell} (member : cell ∈ survivors) : meets cell :=
    of_decide_eq_true (List.mem_filter.mp member).2
  have within : ∀ cell ∈ survivors, firstBank cell ≤ lastBank cell := by
    intro cell member
    have meet := survivor_meets member
    simp only [firstBank, lastBank, dite_eq_left meet]
    exact (traces cell).closed_circle_section_banks_ordered (sections cell meet) nonnegative
      small_error numerical linear_error (margins cell) radius_positive far
  have full_order : P.cells.attach.Pairwise (fun a b => ∀ meet_a meet_b,
      ((traces a).value (a.val.upper.point (sections a meet_a).upperHeight) -
        (traces a).center).re ≤
      ((traces b).value (b.val.lower.point (sections b meet_b).lowerHeight) -
        (traces b).center).re) := by
    rw [List.pairwise_iff_forall_sublist]
    intro a b ordered meet_a meet_b
    exact waterfall_closed_section_facing_bank_order R outward D B leaf_vertices footprint deep
      P traces curvature_covered budget nonnegative small_error linear_error pinches provenance
      represented leaf_coherent numerical margins radius_positive far all_tails continuations
      a b ordered (sections a meet_a) (sections b meet_b)
  have survivors_sublist : survivors.Sublist (P.nonemptyCells cutoff) := List.filter_sublist
  have ordered : survivors.Pairwise (fun a b => lastBank a ≤ firstBank b) := by
    apply List.Pairwise.imp_of_mem _ (full_order.sublist
      (survivors_sublist.trans (P.nonemptyCells_sublist cutoff)))
    intro a b member_a member_b gap
    have meet_a := survivor_meets member_a
    have meet_b := survivor_meets member_b
    simp only [firstBank, lastBank, dite_eq_left meet_a, dite_eq_left meet_b]
    exact gap meet_a meet_b
  have head_meet : meets head := head_meets
  have end_meet : meets endPiece := end_meets
  have close_margin : ε < μ := by nlinarith [sq_nonneg ε]
  have centered (cell : {S : MonotoneStrip // S ∈ P.cells}) (z : ℂ) :
      B.sectorFrame i ((traces cell).outputFrame.symm z -
        D.projectedMap Q (origin)) = z - (traces cell).center := by
    change (traces cell).outputFrame ((traces cell).outputFrame.symm z -
      D.projectedMap Q (origin)) = _
    rw [map_sub, LinearIsometryEquiv.apply_symm_apply, ← (traces cell).center_eq_outputFrame]
  intro cell p member
  obtain ⟨_, ⟨⟨x, approached, rfl⟩, size⟩, rfl⟩ := member
  have meet : meets cell := ⟨_, ⟨x, approached, rfl⟩, size⟩
  have physical := closure_nonempty_iff.mp ⟨x, approached⟩
  have survivor : cell ∈ survivors := List.mem_filter.mpr
    ⟨(P.mem_nonemptyCells cutoff cell).mpr physical, by simpa using meet⟩
  have upper_bound := last_bank_le_of_last firstBank lastBank survivors within ordered
    at_end survivor
  have lower_bound := first_bank_le_of_head firstBank lastBank survivors within ordered
    at_head survivor
  simp only [firstBank, lastBank, dite_eq_left meet, dite_eq_left end_meet,
    dite_eq_left head_meet] at upper_bound lower_bound
  have own := (traces cell).closed_circle_section_point_bounds (sections cell meet) nonnegative
    small_error numerical linear_error (margins cell) radius_positive far approached size
  have first_quadrant := (traces head).strict_quadrant_of_closed_margin close_margin (margins head)
    (sections head head_meets).lower_closed
    ((traces head).closed_circle_height_mem_Ioo radius_positive far
      (sections head head_meets).lower_closed (sections head head_meets).lower_radius).1
  have last_quadrant := (traces cell).strict_quadrant_of_closed_margin close_margin (margins cell)
    (sections cell meet).lower_closed
    ((traces cell).closed_circle_height_mem_Ioo radius_positive far
      (sections cell meet).lower_closed (sections cell meet).lower_radius).1
  have lower_im := complex_im_le_of_norm_eq_of_re_le first_quadrant.1.le last_quadrant.1.le
    first_quadrant.2.le last_quadrant.2.le
    ((sections head head_meets).lower_radius.trans (sections cell meet).lower_radius.symm)
    lower_bound
  have included : cell.val.openSlab 0 cutoff ⊆ (traces cell).strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have closed := closure_mono included approached
  have quadrant := (traces cell).strict_quadrant_of_closed_margin close_margin (margins cell)
    closed ((traces cell).closed_circle_height_mem_Ioo radius_positive far closed size).1
  have actual_size := (traces cell).outputFrame_symm_source_distance ((traces cell).value x)
  rw [size] at actual_size
  constructor
  · refine ⟨?_, ?_, ?_, actual_size⟩
    · rw [centered]; exact quadrant.1.le
    · rw [centered]; exact quadrant.2
    · rw [centered]; exact own.2.1.trans upper_bound
  · refine ⟨?_, ?_, ?_, actual_size⟩
    · rw [centered]; exact quadrant.1.le
    · rw [centered]; exact quadrant.2
    · rw [centered]; exact own.2.2.trans lower_im

end Unfoldings.ConvexRoof.SectorForest
