module

public import Unfoldings.Cap.WaterfallBankControl

/-! The actual selected projected map inherits the uniform containing-face distance bounds. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  {t : ℝ} (positive : 0 < t) (small : t < 1) (D : FacewiseDevelopment C N.retain)
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))

theorem WaterfallBankControl.projectedMap_distance_bounds {ε cutoff : ℝ}
    (control : N.WaterfallBankControl positive small D B ε cutoff) (nonnegative : 0 ≤ ε)
    {p : Plane} (member : p ∈ K.footprint)
    (region : p ∈ sectorSweepInterior positive small source cutoff) :
    (1 - 2 * ε) * ‖p - source‖ ≤ ‖D.projectedMap K p - D.projectedMap K source‖ ∧
      ‖D.projectedMap K p - D.projectedMap K source‖ ≤ (1 + 2 * ε) * ‖p - source‖ := by
  classical
  let f := (Set.mem_iUnion.mp
    (K.footprint_eq_union_projectedTriangles.subset member)).choose
  have on_face : p ∈ (K.projectedTriangle f).carrier :=
    (Set.mem_iUnion.mp (K.footprint_eq_union_projectedTriangles.subset member)).choose_spec
  have bound := control.all_face_distance_bounds N positive small D B nonnegative f on_face region
  simpa only [FacewiseDevelopment.projectedMap, dite_eq_left member] using bound

end Unfoldings.ConvexCap.RadialCutForest
