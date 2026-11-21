module

public import Unfoldings.Roof.AdaptiveCommonForest
public import Unfoldings.Roof.CompatibleMeshCompleteSourceContour

/-! Construct the full intrinsic cut disk and the complete source contour of an adaptive forest. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
/-- The geometric common-potential description preserves precisely the
adaptive cut carriers. Its resulting contour lists every positive source. -/
theorem exists_adaptiveMesh_completeSourceContour {slopes L : Set Plane}
    (convex : Convex ℝ slopes) (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
    {boundary : (frontier slopes).Nonempty} {r margin η : ℝ}
    (R : K.CompatibleAdaptiveRouting {f | K.normalSlope f ∈ slopes}
      (K.clippedExtension slopes compact nonempty) boundary L r margin η)
    (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
    (level : ℝ)
    (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)
    (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
    (positive : 0 < r) (disk : Metric.closedBall (0 : Plane) r ⊆ L)
    {b : ℝ} (bound_pos : 0 < b) (ratio : r ≤ b) (upper : ∀ p ∈ slopes, ‖p‖ ≤ b) :
    let common := R.asCommonPotentialRouting positive disk bound_pos ratio upper
    let β := arccos (r / b)
    let inner_disk : Metric.ball (0 : Plane) r ⊆ slopes :=
      Metric.ball_subset_closedBall.trans (disk.trans R.within)
    let βnonnegative : 0 ≤ β := arccos_nonneg _
    let βacute : β < π / 2 := arccos_lt_pi_div_two.mpr (div_pos positive bound_pos)
    let mesh := K.compatibleCutMesh compact nonempty common no_boundary level higher M positive
      inner_disk
    let forest := K.compatibleMeshForest compact nonempty common no_boundary level higher M positive
      inner_disk βnonnegative βacute
    letI : Fintype mesh.Index := @Fintype.ofFinite _ mesh.finite
    ∃ contour : mesh.pairedComplex.BoundaryContour forest.retain,
      mesh.pairedComplex.contourOriginalVertex forest.selection contour 0 ∈ forest.parents.roots ∧
      mesh.pairedComplex.contourOriginalVertex forest.selection contour (Fin.last contour.length) ∈
        forest.parents.roots ∧
      ∀ v : mesh.pairedComplex.Vertex Set.univ,
        0 < mesh.pairedComplex.interiorAngularDefect Set.univ v →
        ∃ e : mesh.pairedComplex.PositiveContourSource forest.selection contour,
          mesh.pairedComplex.positiveContourVertex forest.selection contour e = v :=
  K.exists_compatibleMesh_completeSourceContour compact nonempty
    (R.asCommonPotentialRouting positive disk bound_pos ratio upper) no_boundary level higher
    positive (Metric.ball_subset_closedBall.trans (disk.trans R.within)) (arccos_nonneg _)
    (arccos_lt_pi_div_two.mpr (div_pos positive bound_pos)) M convex

end Unfoldings.ConvexRoof
