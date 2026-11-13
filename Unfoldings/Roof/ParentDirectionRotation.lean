module

public import Unfoldings.Roof.ProjectionContour
public import Unfoldings.Roof.GermVectors
public import Unfoldings.Development.SubtreeRotation

/-!
# Actual signed parent-direction rotations in a projection-preserving frame

The contour entrance runs toward the child and the exit toward its parent.
Using that actual endpoint order, the exit face's outward parent vector is the
entrance face's vector rotated positively by the whole descendant curvature.
The common complex frame preserves the original projection orientation on all
faces. No nonoverlap or small-curvature premise is used here.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)

/-- One complex frame preserves projected orientation simultaneously on every actual face. -/
theorem projectionContour_frame_positive (D : FacewiseDevelopment C M.retain)
    (f : Face) (a b : Plane) (positive : 0 < orient 0 a b) :
    0 < (starRingEnd ℂ
      (D.boundaryCycleFrame M.projectionContour.cycle (D.roofDirection K f a)) *
      D.boundaryCycleFrame M.projectionContour.cycle (D.roofDirection K f b)).im := by
  rw [D.boundaryCycleFrame_eq_roofProjectionFrame K _ M.projectionContour_positive]
  let P := D.roofProjectionFrame K M.projectionContour.cycle.first.val.1.1
  have cross (x y : Plane) :
      (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm x) *
        Complex.orthonormalBasisOneI.repr.symm y).im = orient 0 x y := by
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      (orient_complex_repr_zero (Complex.orthonormalBasisOneI.repr.symm x)
        (Complex.orthonormalBasisOneI.repr.symm y)).symm
  change 0 < (starRingEnd ℂ
    (Complex.orthonormalBasisOneI.repr.symm (P (D.roofDirection K f a))) *
    Complex.orthonormalBasisOneI.repr.symm (P (D.roofDirection K f b))).im
  rw [cross]
  exact D.roofProjectionFrame_positive K M.duallyConnected _ f a b positive

/-- The actual two parent faces differ by the positive descendant-curvature bank rotation. -/
theorem exists_parent_direction_rotation (D : FacewiseDevelopment C M.retain)
    (e : C.Vertex Set.univ) (nonroot : e ∉ M.parents.roots) :
    ∃ enter leave : Fin (M.projectionContour.length + 1), ∃ side : Bool,
      (C.boundaryEndEquiv M.retain (M.projectionContour.cycle.point enter)).1 =
        C.relativeCutBank M.retain Set.univ (C.selectedParentCut M.selection e nonroot) side ∧
      (C.boundaryEndEquiv M.retain (M.projectionContour.cycle.point leave)).1 =
        C.relativeCutBank M.retain Set.univ (C.selectedParentCut M.selection e nonroot) (!side) ∧
      ¬ C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e enter ∧
      C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e leave ∧
      D.boundaryCycleFrame M.projectionContour.cycle
        (D.roofDirection K (M.projectionContour.cycle.point leave).val.1.1
          (K.projectedVertex (M.parents.parent e) - K.projectedVertex e)) =
        polarRay (M.subtreeCurvature e) *
          D.boundaryCycleFrame M.projectionContour.cycle
            (D.roofDirection K (M.projectionContour.cycle.point enter).val.1.1
              (K.projectedVertex (M.parents.parent e) - K.projectedVertex e)) := by
  let contour := M.projectionContour
  obtain ⟨enter, leave, different, enters, leaves, stable⟩ :=
    C.exists_oriented_subtree_exits M.selection M.roots_eq
      contour.cycle contour.closes contour.covers e nonroot
  obtain ⟨side, first, last, rotation⟩ :=
    D.subtree_rigid_bank_rotation_of_exits M.selection M.roots_eq
      contour.cycle contour.closes contour.covers K.folding e nonroot
      enter leave different enters leaves stable
  have entry := K.projectedGermVector_parent_entrance M.selection e nonroot
    (contour.cycle.point enter) side first enters.1
  have exit := K.projectedGermVector_parent_exit M.selection e nonroot
    (contour.cycle.point leave) (!side) last leaves.1
  have entry_ray := D.roofDirection_boundaryRay K (contour.cycle.point enter)
  have exit_ray := D.roofDirection_boundaryRay K (contour.cycle.point leave)
  rw [entry, D.roofDirection_neg] at entry_ray
  rw [exit] at exit_ray
  change D.boundaryCycleFrame (retain := M.retain) contour.cycle
    (-D.boundaryRay (contour.cycle.point leave)) = polarRay (M.subtreeCurvature e) *
      D.boundaryCycleFrame (retain := M.retain) contour.cycle
        (D.boundaryRay (contour.cycle.point enter)) at rotation
  rw [← entry_ray, ← exit_ray, map_neg, map_neg, mul_neg] at rotation
  exact ⟨enter, leave, side, first, last, enters.1, leaves.1, neg_injective rotation⟩

end Unfoldings.ConvexRoof.SectorForest
