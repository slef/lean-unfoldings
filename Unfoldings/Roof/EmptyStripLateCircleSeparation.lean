module

public import Unfoldings.Roof.EmptyStripChainLateCircleSeparation
public import Unfoldings.Cap.ParentPathCircleBankOrder
public import Unfoldings.Cap.RegularCircleRadius

/-! Separate surviving strip slices beyond an intervening strip's actual terminal height. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outerDomain : Set Plane} {F : K.SkirtTailFamily outerDomain origin}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {i : FiveSector}

/-- The facing endpoints need not be adjacent subdivision cells. A terminated
intermediate strip supplies their common actual fine parent path. No synthetic
comparison chord is assumed to avoid developed surface. -/
theorem circle_slices_disjoint_after_terminal_strip
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest origin (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S T U : MonotoneStrip} {ε μ cutoff physicalRadius radius : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (other : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i T ε cutoff)
    (middle : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i U ε cutoff)
    (tails : U.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    (continuation : B.EmptyCircleContinuation i middle physicalRadius radius)
    (footprint : Q.footprint = outerDomain)
    (deep : Metric.closedBall origin cutoff ⊆ interior (outerDomain))
    (nonnegative : 0 ≤ ε) (small_error : ε < 1 / 2)
    (numerical : ε * (1 + ε) < μ - ε)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement Q
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference)
        (fiveSectorFrame t positive small i).place f).linear z - z‖ ≤ ε * ‖z‖)
    (first_margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (budget : FineC.totalInteriorAngularDefect Set.univ < Real.pi)
    (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
    (outside : radius ∉ D.fiveSectorVertexRadii Q origin
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
    (first_slice : S.BankCircleSlice data.value data.center cutoff radius)
    (last_slice : T.BankCircleSlice other.value other.center cutoff radius)
    (first_wall : S.upper = U.lower) (last_wall : T.lower = U.upper)
    (first_after : continuation.height ≤ first_slice.upperHeight)
    (last_after : continuation.height ≤ last_slice.lowerHeight) :
    Disjoint (data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius})
      (other.value '' T.openSlab 0 cutoff ∩ {z | ‖z - other.center‖ = radius}) := by
  exact circle_slices_disjoint_after_terminal_strip_chain R outward D B data other middle tails
    continuation footprint deep nonnegative small_error numerical linear_error first_margin
    last_margin curvature_covered budget radius_positive far outside first_slice last_slice
    (n := 0) (fun _ => U) (fun j => Fin.elim0 j) 0 rfl first_wall last_wall
    (fun _ => continuation.merged) first_after last_after

end Unfoldings.ConvexRoof.SectorForest
