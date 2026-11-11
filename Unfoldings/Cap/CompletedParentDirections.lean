module

public import Unfoldings.Cap.CompletedForestBanks
public import Unfoldings.Cap.ParentDirectionRotation

/-! Signed actual bank rotations for completed roof forests, in one projection-preserving frame. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)

theorem completedDuallyConnected : C.DuallyConnected R.completedRetain := by
  let : ConnectedSpace (Metric.closedBall (0 : Plane) 1) :=
    isConnected_iff_connectedSpace.mp
      ((convex_closedBall (0 : Plane) 1).isConnected ⟨0, Metric.mem_closedBall_self zero_le_one⟩)
  let : ConnectedSpace (C.Realization R.completedRetain) :=
    R.completedCutDisk.symm.surjective.connectedSpace R.completedCutDisk.symm.continuous
  exact C.duallyConnected_of_preconnected R.completedRetain

def completedSubtreeCurvature (e : C.Vertex Set.univ) : ℝ :=
  ∑ v ∈ R.spanningCompletion.parents.descendants e, C.interiorAngularDefect Set.univ v

theorem completedSubtreeCurvature_nonneg (e : C.Vertex Set.univ) :
    0 ≤ R.completedSubtreeCurvature e :=
  Finset.sum_nonneg (fun v _ => K.interiorCurvature_nonneg v)

theorem completedSubtreeCurvature_le_total (e : C.Vertex Set.univ) :
    R.completedSubtreeCurvature e ≤ C.totalInteriorAngularDefect Set.univ :=
  K.sum_interiorAngularDefect_le_totalCurvature _

/-- One common complex frame has the same orientation as the actual horizontal projection. -/
theorem completedContour_frame_positive (D : FacewiseDevelopment C R.completedRetain)
    (f : Face) (a b : Plane) (positive : 0 < orient 0 a b) :
    0 < (starRingEnd ℂ
      (D.boundaryCycleFrame R.completedContour.cycle (D.developedDirection K f a)) *
      D.boundaryCycleFrame R.completedContour.cycle (D.developedDirection K f b)).im := by
  rw [D.boundaryCycleFrame_eq_projectionFrame K _ R.completedContour_positive]
  let P := D.projectionFrame K R.completedContour.cycle.first.val.1.1
  have cross (x y : Plane) :
      (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm x) *
        Complex.orthonormalBasisOneI.repr.symm y).im = orient 0 x y := by
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      (orient_complex_repr_zero (Complex.orthonormalBasisOneI.repr.symm x)
        (Complex.orthonormalBasisOneI.repr.symm y)).symm
  change 0 < (starRingEnd ℂ
    (Complex.orthonormalBasisOneI.repr.symm (P (D.developedDirection K f a))) *
    Complex.orthonormalBasisOneI.repr.symm (P (D.developedDirection K f b))).im
  rw [cross]
  exact D.projectionFrame_positive K R.completedDuallyConnected _ f a b positive

/-- Entire descendant curvature rotates the two actual outward parent-bank vectors positively.
This also applies to added branches, whose descendant curvature is zero. -/
theorem completed_parent_direction_rotation (D : FacewiseDevelopment C R.completedRetain)
    (e : C.Vertex Set.univ) (nonroot : e ∉ R.spanningCompletion.parents.roots) :
    ∃ enter leave : Fin (R.completedContour.length + 1), ∃ side : Bool,
      (C.boundaryEndEquiv R.completedRetain (R.completedContour.cycle.point enter)).1 =
        C.relativeCutBank R.completedRetain Set.univ
          (C.selectedParentCut R.spanningCompletion.selection e nonroot) side ∧
      (C.boundaryEndEquiv R.completedRetain (R.completedContour.cycle.point leave)).1 =
        C.relativeCutBank R.completedRetain Set.univ
          (C.selectedParentCut R.spanningCompletion.selection e nonroot) (!side) ∧
      ¬ C.SubtreeBoundaryInside R.spanningCompletion.selection R.completedContour.cycle e enter ∧
      C.SubtreeBoundaryInside R.spanningCompletion.selection R.completedContour.cycle e leave ∧
      D.boundaryCycleFrame R.completedContour.cycle
        (D.developedDirection K (R.completedContour.cycle.point leave).val.1.1
          (K.projectedVertex (R.spanningCompletion.parents.parent e) - K.projectedVertex e)) =
        polarRay (R.completedSubtreeCurvature e) *
          D.boundaryCycleFrame R.completedContour.cycle
            (D.developedDirection K (R.completedContour.cycle.point enter).val.1.1
              (K.projectedVertex (R.spanningCompletion.parents.parent e) -
                K.projectedVertex e)) := by
  let contour := R.completedContour
  let S := R.spanningCompletion.selection
  have roots := R.spanningCompletion.roots_eq
  obtain ⟨enter, leave, different, enters, leaves, stable⟩ :=
    C.exists_oriented_subtree_exits S roots contour.cycle contour.closes contour.covers e nonroot
  obtain ⟨side, first, last, rotation⟩ :=
    D.subtree_rigid_bank_rotation_of_exits S roots contour.cycle contour.closes contour.covers
      K.folding e nonroot enter leave different enters leaves stable
  have entry := K.projectedGermVector_parent_entrance S e nonroot
    (contour.cycle.point enter) side first enters.1
  have exit := K.projectedGermVector_parent_exit S e nonroot
    (contour.cycle.point leave) (!side) last leaves.1
  have entry_ray := D.developedDirection_boundaryRay K (contour.cycle.point enter)
  have exit_ray := D.developedDirection_boundaryRay K (contour.cycle.point leave)
  rw [entry, D.developedDirection_neg] at entry_ray
  rw [exit] at exit_ray
  change D.boundaryCycleFrame (retain := R.completedRetain) contour.cycle
    (-D.boundaryRay (contour.cycle.point leave)) = polarRay (R.completedSubtreeCurvature e) *
      D.boundaryCycleFrame (retain := R.completedRetain) contour.cycle
        (D.boundaryRay (contour.cycle.point enter)) at rotation
  rw [← entry_ray, ← exit_ray, map_neg, map_neg, mul_neg] at rotation
  exact ⟨enter, leave, side, first, last, enters.1, leaves.1, neg_injective rotation⟩

end Unfoldings.ConvexCap.RadialCutForest
