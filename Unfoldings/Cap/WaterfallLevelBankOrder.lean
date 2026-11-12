module

public import Unfoldings.Cap.GeometricLevelBankOrder
public import Unfoldings.Cap.RadialStripLevelOrder
public import Unfoldings.Cap.FramedVertexHeights
public import Unfoldings.Geometry.SubdivisionActiveCells
public import Unfoldings.Topology.OrderedBankPieces

/-! All surviving actual bank intervals are ordered at every regular physical sweep height. -/

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

/-- This keeps the actual subdivision order and permits any number of collapsed
cells between two positive-width cells. It supplies both coordinate inequalities. -/
theorem waterfall_level_bank_pairwise
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
    {h : ℝ} (height : h ∈ Set.Ioo 0 cutoff)
    (outside : h ∉ Q.framedVertexHeights (K.projectedVertex origin)
      (fiveSectorFrame t positive small i).place) :
    (P.activeCells h).Pairwise (fun first last =>
      ((traces first).value (first.val.upper.point h)).re ≤
          ((traces last).value (last.val.lower.point h)).re ∧
        ((traces last).value (last.val.lower.point h)).im ≤
          ((traces first).value (first.val.upper.point h)).im) := by
  let first : {S : MonotoneStrip // S ∈ P.cells} → ℝ × ℝᵒᵈ := fun cell =>
    (((traces cell).value (cell.val.lower.point h)).re,
      ((traces cell).value (cell.val.lower.point h)).im)
  let last : {S : MonotoneStrip // S ∈ P.cells} → ℝ × ℝᵒᵈ := fun cell =>
    (((traces cell).value (cell.val.upper.point h)).re,
      ((traces cell).value (cell.val.upper.point h)).im)
  change (P.activeCells h).Pairwise (fun a b => last a ≤ first b)
  apply ordered_bank_pieces_pairwise first last (P.activeCells h)
  · intro cell active
    have width := (P.mem_activeCells h cell).mp active
    have closed := cell.val.bank_points_mem_closure_of_width ⟨height.1.le, height.2.le⟩ width
    exact (traces cell).same_height_order nonnegative small_error linear_error closed.1 closed.2
      (cell.val.ordered h) (by rw [cell.val.lower.point_height, cell.val.upper.point_height])
  · apply List.IsChain.imp_of_mem_imp _ (P.activeCells_bank_point_chain h)
    intro a b first_active last_active same_point
    have regular := Q.regular_of_not_framedVertexHeights (K.projectedVertex origin)
      (fiveSectorFrame t positive small i).place (z := a.val.upper.point h)
      (by simpa only [a.val.upper.point_height] using outside)
    exact regular_level_bank_order R outward D B leaf_vertices footprint deep P
      a.property b.property
      (traces a) (traces b) curvature_covered budget height
      ((P.mem_activeCells h a).mp first_active) ((P.mem_activeCells h b).mp last_active)
      same_point regular

end Unfoldings.ConvexCap.SectorForest
