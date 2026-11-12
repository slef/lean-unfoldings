module

public import Unfoldings.Cap.ContactSeparatorPrefix
public import Unfoldings.Cap.ContactTraceValues
public import Unfoldings.Cap.RadialStripClosedBanks
public import Unfoldings.Geometry.SubdivisionBankContact
public import Unfoldings.Cap.TerminalHeightLeafOrder
public import Unfoldings.Cap.ApproachedVertexPinchWidth
public import Unfoldings.Cap.EmptyCircleContinuation
public import Unfoldings.Cap.RegularCircleRadius
public import Unfoldings.Cap.RadialStripCircleWidth
public import Unfoldings.Geometry.StripSlabApproach

/-! A surviving circle crossing lies beyond its shared leaf when its neighbor has disappeared. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {i : FiveSector}
  (leaf : M.GeometricSectorLeaf F covered positive small lower i)
  {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
  {Q : ConvexCap FineC}
  (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
  (D : FacewiseDevelopment FineC R.retain)
  (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
  {cutoff ε physicalRadius radius : ℝ}
  (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
  (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
  (represented : ∀ w : M.GeometricSectorLeaf F covered positive small lower i,
    w.point.re + w.point.im ≤ cutoff → ∃ G ∈ P.separators,
      MonotoneStrip.CompletesTail w.point w.tailGraph.graph cutoff G)
  (traces : ∀ S ∈ P.cells, Nonempty (R.RadialStripTraceData positive small D
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff))
  (active : leaf.point.re + leaf.point.im ≤ cutoff)
  (leaf_coherent : D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
  {S U : MonotoneStrip} (cell : S ∈ P.cells) (middle_cell : U ∈ P.cells)
  (data : R.RadialStripTraceData positive small D
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
  (middle : R.RadialStripTraceData positive small D
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i U ε cutoff)
  (tails : U.TerminalTailsFrom
    (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
    (fun leaf => leaf.tailGraph.graph) cutoff)
  (pinches : U.ApproachedPinchesIn
    (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
        M.extendedGeometricCuts F} =>
      (fiveSectorFrame t positive small i).place
        (Q.projectedVertex v.val - K.projectedVertex origin))) 0 cutoff)
  (continuation : B.EmptyCircleContinuation i middle physicalRadius radius)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
  (outside_vertices : radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
  (outside_middle : radius ∉ middle.emptyCircleExceptions)
  (empty : middle.value '' U.openSlab 0 cutoff ∩ {z | ‖z - middle.center‖ = radius} = ∅)
  (slice : S.BankCircleSlice data.value data.center cutoff radius)

include deep represented traces active leaf_coherent cell middle_cell tails pinches continuation
  radius_positive far outside_vertices outside_middle empty

/-- Removing empty physical cells preserves enough contact to exclude a
surviving circle crossing on the coherent prefix of its own separator. -/
theorem upper_circle_after_empty_neighbor_leaf_of_contact
    (separator : S.upper ∈ P.separators)
    (wall : Set.EqOn S.upper.point U.lower.point (Set.Icc 0 cutoff))
    (completion : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff S.upper) :
    leaf.point.re + leaf.point.im < slice.upperHeight := by
  by_contra before
  have prefix_height : slice.upperHeight ≤ leaf.point.re + leaf.point.im := not_lt.mp before
  have terminal := leaf.le_permanent_terminal_height_of_contact deep tails completion active
    continuation.height_bounds continuation.merged
    (Or.inl (fun h member => wall ⟨continuation.height_bounds.1.le.trans member.1, member.2⟩))
  have height := (data.circle_slice_heights radius_positive far slice).2
  have contact := wall ⟨height.1.le, height.2.le⟩
  have regular := data.regular_of_radius_not_vertexRadii outside_vertices slice.upper_closed
    slice.upper_radius
  have included : U.openSlab 0 cutoff ⊆ middle.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have terminal_closed := closure_mono included continuation.lower_closed
  have closed := middle.lower_bank_closed_before terminal_closed
    (by rw [U.lower.point_height]; exact ⟨height.1.le, prefix_height.trans terminal⟩)
  have width := middle.width_pos_of_approached_regular pinches height closed
    (by rw [← contact]; exact regular)
  have inside := P.bank_contact_mem_strictCarrier cell middle_cell contact
    (data.circle_slice_width radius_positive slice).2 width
  have coherent := leaf.separator_prefix_coherent R D _ deep P represented traces separator active
    completion leaf_coherent ⟨height.1.le, prefix_height⟩ inside
  have equal := data.value_eq_of_coherent_contact middle contact slice.upper_closed closed coherent
  have approached := U.mem_closure_openSlab_of_height closed
    (by rw [U.lower.point_height]; exact height)
  have bound := middle.closed_inside_of_empty_circle radius_positive outside_middle empty approached
  rw [← equal] at bound
  exact (not_lt_of_ge slice.upper_radius.ge) bound

/-- The right surviving cell uses its own lower separator; the deleted cells
need only identify that separator with the empty neighbor on this slab. -/
theorem lower_circle_after_empty_neighbor_leaf_of_contact
    (separator : S.lower ∈ P.separators)
    (wall : Set.EqOn S.lower.point U.upper.point (Set.Icc 0 cutoff))
    (completion : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff S.lower) :
    leaf.point.re + leaf.point.im < slice.lowerHeight := by
  by_contra before
  have prefix_height : slice.lowerHeight ≤ leaf.point.re + leaf.point.im := not_lt.mp before
  have terminal := leaf.le_permanent_terminal_height_of_contact deep tails completion active
    continuation.height_bounds continuation.merged
    (Or.inr (fun h member => wall ⟨continuation.height_bounds.1.le.trans member.1, member.2⟩))
  have height := (data.circle_slice_heights radius_positive far slice).1
  have contact := wall ⟨height.1.le, height.2.le⟩
  have regular := data.regular_of_radius_not_vertexRadii outside_vertices slice.lower_closed
    slice.lower_radius
  have included : U.openSlab 0 cutoff ⊆ middle.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have terminal_closed := closure_mono included continuation.upper_closed
  have closed := middle.upper_bank_closed_before terminal_closed
    (by rw [U.upper.point_height]; exact ⟨height.1.le, prefix_height.trans terminal⟩)
  have width := middle.width_pos_of_upper_approached_regular pinches height closed
    (by rw [← contact]; exact regular)
  have inside := P.bank_contact_mem_strictCarrier middle_cell cell contact.symm width
    (data.circle_slice_width radius_positive slice).1
  have coherent := leaf.separator_prefix_coherent R D _ deep P represented traces separator active
    completion leaf_coherent ⟨height.1.le, prefix_height⟩ (by rw [contact]; exact inside)
  have equal := data.value_eq_of_coherent_contact middle contact slice.lower_closed closed coherent
  have approached := U.mem_closure_openSlab_of_height closed
    (by rw [U.upper.point_height]; exact height)
  have bound := middle.closed_inside_of_empty_circle radius_positive outside_middle empty approached
  rw [← equal] at bound
  exact (not_lt_of_ge slice.lower_radius.ge) bound

end Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf

