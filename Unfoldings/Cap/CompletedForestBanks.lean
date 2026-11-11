module

public import Unfoldings.Cap.RadialForestCompletion
public import Unfoldings.Cap.ProjectionContour
public import Unfoldings.Complex.BoundaryContour
public import Unfoldings.Development.AdditionalCuts
public import Unfoldings.Development.SubtreeRotation

/-! Actual bank openings for completed extended forests, including zero-curvature added branches. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)

def completedContour : C.BoundaryContour R.completedRetain :=
  Classical.choose (K.exists_projection_positive_contour R.completedRetain
    (K.folding.boundaryGraph_connected_of_disk R.completedRetain R.completedCutDisk))

theorem completedContour_positive :
    0 < K.projectedGermOrientation R.completedContour.cycle.first.val :=
  Classical.choose_spec (K.exists_projection_positive_contour R.completedRetain
    (K.folding.boundaryGraph_connected_of_disk R.completedRetain R.completedCutDisk))

/-- The actual two parent banks differ by exactly the total descendant curvature. The complete
boundary contour comes from the constructed cut disk, independently of overlap. -/
theorem completed_subtree_bank_rotation (D : FacewiseDevelopment C R.completedRetain)
    (e : C.Vertex Set.univ) (nonroot : e ∉ R.spanningCompletion.parents.roots) :
    ∃ enter leave : Fin (R.completedContour.length + 1), ∃ side : Bool,
      (C.boundaryEndEquiv R.completedRetain (R.completedContour.cycle.point enter)).1 =
        C.relativeCutBank R.completedRetain Set.univ
          (C.selectedParentCut R.spanningCompletion.selection e nonroot) side ∧
      (C.boundaryEndEquiv R.completedRetain (R.completedContour.cycle.point leave)).1 =
        C.relativeCutBank R.completedRetain Set.univ
          (C.selectedParentCut R.spanningCompletion.selection e nonroot) (!side) ∧
      D.boundaryCycleFrame R.completedContour.cycle
          (-D.boundaryRay (R.completedContour.cycle.point leave)) =
        polarRay (∑ v ∈ R.spanningCompletion.parents.descendants e,
          C.interiorAngularDefect Set.univ v) *
            D.boundaryCycleFrame R.completedContour.cycle
              (D.boundaryRay (R.completedContour.cycle.point enter)) :=
  D.exists_subtree_rigid_bank_rotation R.spanningCompletion.selection
    R.spanningCompletion.roots_eq R.completedContour.cycle R.completedContour.closes
    R.completedContour.covers K.folding e nonroot

/-- Added branches outside the curvature-carrying cut set have zero aperture in every actual
development of the completed cut disk. The bank labels remain distinct. -/
theorem completed_extra_bank_parallel (D : FacewiseDevelopment C R.completedRetain)
    (covered : ∀ w : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ w →
      K.projectedVertex w ∈ cuts)
    (e : C.Vertex Set.univ) (outside : K.projectedVertex e ∉ cuts)
    (nonroot : e ∉ R.spanningCompletion.parents.roots) :
    ∃ enter leave : Fin (R.completedContour.length + 1), ∃ side : Bool,
      (C.boundaryEndEquiv R.completedRetain (R.completedContour.cycle.point enter)).1 =
        C.relativeCutBank R.completedRetain Set.univ
          (C.selectedParentCut R.spanningCompletion.selection e nonroot) side ∧
      (C.boundaryEndEquiv R.completedRetain (R.completedContour.cycle.point leave)).1 =
        C.relativeCutBank R.completedRetain Set.univ
          (C.selectedParentCut R.spanningCompletion.selection e nonroot) (!side) ∧
      -D.boundaryRay (R.completedContour.cycle.point leave) =
        D.boundaryRay (R.completedContour.cycle.point enter) := by
  obtain ⟨enter, leave, side, first, last, rotation⟩ :=
    R.completed_subtree_bank_rotation D e nonroot
  rw [R.completed_extra_subtree_zero covered e outside, polarRay_zero, one_mul] at rotation
  exact ⟨enter, leave, side, first, last,
    (D.boundaryCycleFrame R.completedContour.cycle).injective rotation⟩

/-- Reuse the minimal cut development, adding only redundant seam cuts with unchanged placements. -/
def completedDevelopment (D : FacewiseDevelopment C R.retain) :
    FacewiseDevelopment C R.completedRetain := D.cut R.completedRetain_subset

@[simp] theorem completedDevelopment_nonoverlapping_iff (D : FacewiseDevelopment C R.retain) :
    (R.completedDevelopment D).Nonoverlapping ↔ D.Nonoverlapping := Iff.rfl

/-- A seam newly cut only for completion still matches pointwise in this chosen development. -/
theorem completed_added_seam_joined (D : FacewiseDevelopment C R.retain)
    (s : C.Seam) (retained : s ∈ R.retain)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge) :
    (R.completedDevelopment D).place (C.left s).face x =
      (R.completedDevelopment D).place (C.right s).face (C.identify s x) :=
  D.joined s retained x

end Unfoldings.ConvexCap.RadialCutForest
