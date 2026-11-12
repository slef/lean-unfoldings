module

public import Unfoldings.Cap.WaterfallCircleSurvivorBanks
public import Unfoldings.Cap.StripCircleCoordinateCaps
public import Unfoldings.Topology.OrderedBankEndpoints
public import Unfoldings.Topology.OrderedBankPieces
public import Unfoldings.Topology.FilterDisjoint

/-! Every actual sector circle image lies between the extreme surviving bank bounds. -/

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
          (Q.projectedVertex v.val - K.projectedVertex origin))) 0 cutoff)

variable
  (provenance : ∀ H ∈ P.separators,
    ∃ leaf : M.GeometricSectorLeaf F covered positive small lower i,
      leaf.point.re + leaf.point.im ≤ cutoff ∧
        MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
  (represented : ∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
    leaf.point.re + leaf.point.im ≤ cutoff → ∃ H ∈ P.separators,
      MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
  (leaf_coherent : ∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
    D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))

variable {physicalRadius radius : ℝ}

variable {μ : ℝ} (numerical : ε * (1 + ε) < μ - ε)
  (margins : ∀ cell : {S : MonotoneStrip // S ∈ P.cells}, ∀ z ∈ cell.val.carrier,
    0 ≤ z.re + z.im → μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
  (outside : radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)

variable (all_tails : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
    cell.val.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
  (continuations : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
    (traces cell).value '' cell.val.openSlab 0 cutoff ∩
        {z | ‖z - (traces cell).center‖ = radius} = ∅ →
      (cell.val.openSlab 0 cutoff).Nonempty →
        Nonempty (B.EmptyCircleContinuation i (traces cell) physicalRadius radius))
  (all_outside_empty : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
    radius ∉ (traces cell).emptyCircleExceptions)

include outward leaf_vertices footprint deep curvature_covered budget nonnegative
  small_error linear_error pinches provenance represented leaf_coherent numerical margins
  radius_positive far outside all_tails continuations all_outside_empty

open Classical in
theorem waterfall_circle_images_subset_extreme_caps
    (slices : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      ((traces cell).value '' cell.val.openSlab 0 cutoff ∩
        {z | ‖z - (traces cell).center‖ = radius}).Nonempty →
      cell.val.BankCircleSlice (traces cell).value (traces cell).center cutoff radius)
    (head endPiece : {S : MonotoneStrip // S ∈ P.cells})
    (head_meets : ((traces head).value '' head.val.openSlab 0 cutoff ∩
      {z | ‖z - (traces head).center‖ = radius}).Nonempty)
    (end_meets : ((traces endPiece).value '' endPiece.val.openSlab 0 cutoff ∩
      {z | ‖z - (traces endPiece).center‖ = radius}).Nonempty)
    (at_head : ((P.nonemptyCells cutoff).filter (fun cell => decide
      ((traces cell).value '' cell.val.openSlab 0 cutoff ∩
        {z | ‖z - (traces cell).center‖ = radius}).Nonempty)).head? = some head)
    (at_end : ((P.nonemptyCells cutoff).filter (fun cell => decide
      ((traces cell).value '' cell.val.openSlab 0 cutoff ∩
        {z | ‖z - (traces cell).center‖ = radius}).Nonempty)).getLast? = some endPiece) :
    ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      (traces cell).outputFrame.symm '' ((traces cell).value '' cell.val.openSlab 0 cutoff ∩
          {z | ‖z - (traces cell).center‖ = radius}) ⊆
        circleUpperCap (B.sectorFrame i) (D.projectedMap Q (K.projectedVertex origin)) radius
          ((traces endPiece).value
            (endPiece.val.upper.point (slices endPiece end_meets).upperHeight) -
              (traces endPiece).center).re ∩
        circleLowerCap (B.sectorFrame i) (D.projectedMap Q (K.projectedVertex origin)) radius
          ((traces head).value (head.val.lower.point (slices head head_meets).lowerHeight) -
            (traces head).center).im := by
  let meets := fun cell : {S : MonotoneStrip // S ∈ P.cells} =>
    ((traces cell).value '' cell.val.openSlab 0 cutoff ∩
      {z | ‖z - (traces cell).center‖ = radius}).Nonempty
  let keep := fun cell => decide (meets cell)
  let survivors := (P.nonemptyCells cutoff).filter keep
  let firstBank := fun cell => if meet : meets cell then
    let z := (traces cell).value (cell.val.lower.point (slices cell meet).lowerHeight) -
      (traces cell).center
    (z.re, -z.im) else (0, 0)
  let lastBank := fun cell => if meet : meets cell then
    let z := (traces cell).value (cell.val.upper.point (slices cell meet).upperHeight) -
      (traces cell).center
    (z.re, -z.im) else (0, 0)
  have survivor_meets {cell} (member : cell ∈ survivors) : meets cell :=
    of_decide_eq_true (List.mem_filter.mp member).2
  have own_order (cell) (meet : meets cell) := (traces cell).bank_circle_order nonnegative
    small_error numerical linear_error (margins cell) radius_positive
    (slices cell meet).lower_closed (slices cell meet).upper_closed
    (slices cell meet).lower_radius (slices cell meet).upper_radius (slices cell meet).distinct
  have within : ∀ cell ∈ survivors, firstBank cell ≤ lastBank cell := by
    intro cell member
    have meet := survivor_meets member
    simp only [firstBank, lastBank, dite_eq_left meet]
    exact ⟨(own_order cell meet).1.le, neg_le_neg (own_order cell meet).2.le⟩
  have banks_ordered := waterfall_circle_survivor_banks_ordered R outward D B leaf_vertices
    footprint deep P traces curvature_covered budget nonnegative small_error linear_error pinches
    provenance represented leaf_coherent numerical margins radius_positive far outside all_tails
    continuations all_outside_empty slices
  have ordered : survivors.Pairwise (fun a b => lastBank a ≤ firstBank b) := by
    apply List.Pairwise.imp_of_mem _ banks_ordered
    intro a b member_a member_b gap
    have meet_a := survivor_meets member_a
    have meet_b := survivor_meets member_b
    simp only [firstBank, lastBank, dite_eq_left meet_a, dite_eq_left meet_b]
    exact ⟨(gap meet_a meet_b).1, neg_le_neg (gap meet_a meet_b).2⟩
  have close_margin : ε < μ := by nlinarith [sq_nonneg ε]
  have head_meet : meets head := head_meets
  have end_meet : meets endPiece := end_meets
  intro cell p member
  have meet : meets cell := by
    obtain ⟨z, inside, _⟩ := member
    exact ⟨z, inside⟩
  have physical : (cell.val.openSlab 0 cutoff).Nonempty := by
    obtain ⟨_, ⟨z, inside, _⟩, _⟩ := meet
    exact ⟨z, inside⟩
  have survivor : cell ∈ survivors := List.mem_filter.mpr
    ⟨(P.mem_nonemptyCells cutoff cell).mpr physical,
      by simpa only [keep, decide_eq_true_eq] using meet⟩
  have upper := last_bank_le_of_last firstBank lastBank survivors within ordered at_end survivor
  have lower := first_bank_le_of_head firstBank lastBank survivors within ordered at_head survivor
  simp only [lastBank, dite_eq_left meet, dite_eq_left end_meet] at upper
  simp only [firstBank, dite_eq_left meet, dite_eq_left head_meet] at lower
  constructor
  · apply circleUpperCap_mono (B.sectorFrame i) (D.projectedMap Q (K.projectedVertex origin))
      radius upper.1
    exact B.circle_image_subset_upper_cap i (traces cell) (slices cell meet) (own_order cell meet).1
      close_margin (margins cell) radius_positive member
  · apply circleLowerCap_mono (B.sectorFrame i) (D.projectedMap Q (K.projectedVertex origin))
      radius (neg_le_neg_iff.mp lower.2)
    exact B.circle_image_subset_lower_cap i (traces cell) (slices cell meet) (own_order cell meet).1
      close_margin (margins cell) radius_positive member

end Unfoldings.ConvexCap.SectorForest

