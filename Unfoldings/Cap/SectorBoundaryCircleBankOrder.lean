module

public import Unfoldings.Cap.SectorBoundaryBankGeometry
public import Unfoldings.Cap.CrossFrameCircleBankOrder
public import Unfoldings.Cap.CrossFrameTraceQuadrants
public import Unfoldings.Cap.RegularCircleRadius

/-! Actual circle banks facing a radial sector boundary have derived cross-sector order. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  (positive : 0 < t) (small : t < 1)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (lower : Z < 0)

include covered lower

/-- Both traces use their own sector frames. Physical component geometry,
named bank matching, actual face margins, and finite vertex-radius avoidance
derive their order in the first sector's comparison frame. -/
theorem sector_boundary_circle_bank_order
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {i j : FiveSector} {S T : MonotoneStrip} {ε cutoff radius : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (other : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) j T ε cutoff)
    (nonnegative : 0 ≤ ε) (small_error : ε < 1 / 2)
    (radius_positive : 0 < radius) (room : 2 * radius < (1 / 2 - ε) * cutoff)
    (first_slice : S.BankCircleSlice data.value data.center cutoff radius)
    (last_slice : T.BankCircleSlice other.value other.center cutoff radius)
    (outside : radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (budget : FineC.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (face_bounds : ∀ f p, p ∈ (Q.projectedTriangle f).carrier →
      p - K.projectedVertex origin ∈ closedFiveSector t i →
      p ∈ sectorSweepInterior positive small (K.projectedVertex origin) cutoff →
      ε * ‖p - K.projectedVertex origin‖ ≤
        (B.sectorFrame i (D.projectedPlacement Q f p -
          D.projectedMap Q (K.projectedVertex origin))).re ∧
      ε * ‖p - K.projectedVertex origin‖ ≤
        (B.sectorFrame i (D.projectedPlacement Q f p -
          D.projectedMap Q (K.projectedVertex origin))).im)
    (w : FineC.Vertex Set.univ) (c : F.Component)
    (member : Q.projectedVertex w ∈ (F.componentTail c).carrier)
    (boundary : ∀ k, Q.projectedVertex w - K.projectedVertex origin ∉ strictFiveSector t k)
    (first_cone : Q.projectedVertex w - K.projectedVertex origin ∈ closedFiveSector t i)
    (last_cone : Q.projectedVertex w - K.projectedVertex origin ∈ closedFiveSector t j)
    (a b : Fin (R.spanningCompletion.parents.distanceToRoot w)) (s r : unitInterval)
    (first_physical : K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point first_slice.upperHeight) = (R.completedRootPath w).point a s)
    (last_physical : K.projectedVertex origin + (fiveSectorFrame t positive small j).place.symm
      (T.lower.point last_slice.lowerHeight) = (R.completedRootPath w).point b r) :
    (B.sectorFrame i
      (data.outputFrame.symm (data.value (S.upper.point first_slice.upperHeight)) -
        D.projectedMap Q (K.projectedVertex origin))).re ≤
      (B.sectorFrame i
        (other.outputFrame.symm (other.value (T.lower.point last_slice.lowerHeight)) -
          D.projectedMap Q (K.projectedVertex origin))).re ∧
    (B.sectorFrame i
      (other.outputFrame.symm (other.value (T.lower.point last_slice.lowerHeight)) -
        D.projectedMap Q (K.projectedVertex origin))).im ≤
      (B.sectorFrame i
        (data.outputFrame.symm (data.value (S.upper.point first_slice.upperHeight)) -
          D.projectedMap Q (K.projectedVertex origin))).im := by
  obtain ⟨positions, first_directions, sectors⟩ := M.sector_boundary_completed_bank_geometry
    positive small F covered lower R outward curvature_covered w c member boundary i first_cone
  obtain ⟨_, last_directions, _⟩ := M.sector_boundary_completed_bank_geometry
    positive small F covered lower R outward curvature_covered w c member boundary j last_cone
  have on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F := by
    rw [M.extendedGeometricCuts_eq_piece_union F]
    exact Set.mem_iUnion.mpr ⟨Sum.inr c, member⟩
  have first_position := R.completedRootPath_point_in_sector i w positions a s
  have last_position := R.completedRootPath_point_in_sector i w positions b r
  rw [← first_physical, add_sub_cancel_left] at first_position
  rw [← last_physical, add_sub_cancel_left] at last_position
  have first_quadrant := data.closed_circle_quadrant_in_sector nonnegative small_error
    first_slice.upper_closed first_slice.upper_radius room i (B.sectorFrame i)
    (D.projectedMap Q (K.projectedVertex origin)) face_bounds first_position
  have last_quadrant := other.closed_circle_quadrant_in_sector nonnegative small_error
    last_slice.lower_closed last_slice.lower_radius room i (B.sectorFrame i)
    (D.projectedMap Q (K.projectedVertex origin)) face_bounds last_position
  have far : radius < (1 / 2 - ε) * cutoff := (by linarith : radius < 2 * radius).trans room
  exact B.circle_parent_path_bank_order_across_frames i j i data other radius_positive far
    first_slice last_slice w on_cuts first_directions last_directions first_directions sectors
    budget a b s r
    (data.regular_of_radius_not_vertexRadii outside
      first_slice.upper_closed first_slice.upper_radius)
    (other.regular_of_radius_not_vertexRadii outside
      last_slice.lower_closed last_slice.lower_radius)
    first_physical last_physical first_quadrant last_quadrant

end Unfoldings.ConvexCap.SectorForest
