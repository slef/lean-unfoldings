module

public import Unfoldings.Cap.OuterCircleCaps
public import Unfoldings.Cap.BoundaryComponentFineSeed
public import Unfoldings.Cap.SharedEndpointCircleSeparation
public import Unfoldings.Cap.SharedBoundaryBankMargins
public import Unfoldings.Cap.ComponentBankCircleSeparation
public import Unfoldings.Cap.RadialComponentCircleBanks

/-! Adjacent outer surviving strips separate even when their shared ray is cut. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1) (lower : Z < 0)

theorem circle_images_disjoint_across_shared_outer_banks
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    (leaf_vertices : ∀ a, ∀ leaf : M.GeometricSectorLeaf F covered positive small lower a,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (leaf_coherent : ∀ a, ∀ leaf : M.GeometricSectorLeaf F covered positive small lower a,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    (footprint : Q.footprint = K.clipFootprint Z)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (budget : FineC.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    {i j : FiveSector} (shared : fiveSectorFirst t i = fiveSectorLast t j)
    {S T : MonotoneStrip} {ε cutoff radius : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (other : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) j T ε cutoff)
    (slice : S.BankCircleSlice data.value data.center cutoff radius)
    (other_slice : T.BankCircleSlice other.value other.center cutoff radius)
    (first_outer : Set.EqOn S.upper.point
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff))
    (last_outer : Set.EqOn T.lower.point
      (fiveSectorFrame t positive small j).enclosingStrip.lower.point (Set.Icc 0 cutoff))
    (first_order : (data.value (S.lower.point slice.lowerHeight) - data.center).re <
      (data.value (S.upper.point slice.upperHeight) - data.center).re)
    (last_order : (other.value (T.lower.point other_slice.lowerHeight) - other.center).re <
      (other.value (T.upper.point other_slice.upperHeight) - other.center).re)
    {μ ν ω : ℝ} (first_error : ε < μ) (last_error : ε < ν)
    (first_margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      ν * (z.re + z.im) ≤ z.re ∧ ν * (z.re + z.im) ≤ z.im)
    (radius_positive : 0 < radius) (small_error : ε < 1 / 2)
    (room : 2 * radius < (1 / 2 - ε) * cutoff)
    (outside : radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    (positive_margin : 0 < ω)
    (face_bounds : ∀ a f p, p ∈ (Q.projectedTriangle f).carrier →
      p - K.projectedVertex origin ∈ closedFiveSector t a →
      p ∈ sectorSweepInterior positive small (K.projectedVertex origin) cutoff →
      ω * ‖p - K.projectedVertex origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q (K.projectedVertex origin))).re ∧
      ω * ‖p - K.projectedVertex origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q (K.projectedVertex origin))).im) :
    Disjoint (data.outputFrame.symm '' (data.value '' S.openSlab 0 cutoff ∩
        {z | ‖z - data.center‖ = radius}))
      (other.outputFrame.symm '' (other.value '' T.openSlab 0 cutoff ∩
        {z | ‖z - other.center‖ = radius})) := by
  have caps := M.circle_caps_disjoint_across_shared_outer_banks F covered positive small lower
    R outward D B leaf_vertices leaf_coherent footprint curvature_covered budget shared data other
    slice other_slice first_outer last_outer radius_positive small_error room outside deep
    positive_margin face_bounds
  exact caps.mono
    (B.circle_image_subset_upper_cap i data slice first_order first_error first_margin
      radius_positive)
    (B.circle_image_subset_lower_cap j other other_slice last_order last_error last_margin
      radius_positive)

end Unfoldings.ConvexCap.SectorForest
