module

public import Unfoldings.Cap.SubtreeAngles
public import Unfoldings.Development.SubtreeRotation
public import Unfoldings.Cone.PolarEquality

/-!
# Actual rigid bank openings for whole branching cap subtrees

The two distinctly named banks of the original parent seam have matched lengths.
In one common boundary frame their vectors, directed the same way, differ by
an actual rigid rotation through the sum of all descendant curvatures. If the
cap's total curvature is at most pi, that sum is the genuine bank aperture.
Zero curvature permits coincident directions and boundary contact.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- Whole-subtree bank opening, including actual original seam names and every attached branch. -/
theorem exists_subtree_rigid_bank_opening (D : FacewiseDevelopment C M.retain)
    (e : C.Vertex Set.univ) (nonroot : e ∉ M.parents.roots)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi) :
    ∃ enter leave : Fin (M.contour.length + 1), ∃ side : Bool,
      (C.boundaryEndEquiv M.retain (M.contour.cycle.point enter)).1 =
        C.relativeCutBank M.retain Set.univ (C.selectedParentCut M.selection e nonroot) side ∧
      (C.boundaryEndEquiv M.retain (M.contour.cycle.point leave)).1 =
        C.relativeCutBank M.retain Set.univ (C.selectedParentCut M.selection e nonroot) (!side) ∧
      D.boundaryCycleFrame M.contour.cycle (-D.boundaryRay (M.contour.cycle.point leave)) =
        polarRay (M.subtreeCurvature e) *
          D.boundaryCycleFrame M.contour.cycle (D.boundaryRay (M.contour.cycle.point enter)) ∧
      InnerProductGeometry.angle (D.boundaryRay (M.contour.cycle.point enter))
        (-D.boundaryRay (M.contour.cycle.point leave)) = M.subtreeCurvature e := by
  obtain ⟨enter, leave, side, first, last, rotation⟩ :=
    D.exists_subtree_rigid_bank_rotation M.selection M.roots_eq
      M.contour.cycle M.contour.closes M.contour.covers K.folding e nonroot
  let L := D.boundaryCycleFrame M.contour.cycle
  let x := D.boundaryRay (M.contour.cycle.point enter)
  let y := -D.boundaryRay (M.contour.cycle.point leave)
  have genuine : L x ≠ 0 := by
    simpa only [map_zero] using L.injective.ne (D.boundaryRay_ne_zero (M.contour.cycle.point enter))
  have nonnegative := M.subtreeCurvature_nonneg e
  have small := (M.subtreeCurvature_le_total e).trans budget
  change L y = polarRay (M.subtreeCurvature e) * L x at rotation
  refine ⟨enter, leave, side, first, last, rotation, ?_⟩
  calc
    _ = InnerProductGeometry.angle (L x) (L y) := (L.toLinearIsometry.angle_map _ _).symm
    _ = InnerProductGeometry.angle (1 * L x) (polarRay (M.subtreeCurvature e) * L x) := by
      rw [rotation, one_mul]
    _ = InnerProductGeometry.angle 1 (polarRay (M.subtreeCurvature e)) :=
      Complex.angle_mul_right genuine _ _
    _ = _ := by
      simpa only [polarRay_zero, sub_zero] using
        angle_polarRay 0 (M.subtreeCurvature e) (by simpa using nonnegative) (by simpa using small)

end Unfoldings.ConvexCap.SectorForest
