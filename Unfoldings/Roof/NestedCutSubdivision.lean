module

public import Unfoldings.Roof.NestedMeshCutGeometry
public import Unfoldings.Roof.NestedSubdivisionAngles
public import Unfoldings.Complex.SubdivisionPhysicalConforming

/-! Actual cuts on nested roof triangulations preserve original retained seam classes and fans. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z W : ℝ} (T : Triangulation family Z) (U : Triangulation family W)

local instance nestedConformingOldFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite
local instance nestedConformingNewFintype : Fintype U.Index := @Fintype.ofFinite _ U.finite

/-- Horizontal cuts avoiding old projected face interiors avoid their true metric interiors. -/
theorem physical_cut_disjoint_face_interior (cuts : Set Plane)
    (outside : ∀ f, Disjoint (interior (T.projectedTriangle f).carrier) cuts) (f : T.Index) :
    Disjoint (interior (T.triangle f).carrier)
      (T.pairedFolding.place f ⁻¹' (Cap.horizontal ⁻¹' cuts)) := by
  apply Set.disjoint_left.mpr
  intro z inside on_cut
  let H := (family (T.support f)).project.symm.toContinuousAffineEquiv.toHomeomorph
  rw [T.triangle_carrier] at inside
  change z ∈ interior (H '' (T.projectedTriangle f).carrier) at inside
  rw [← H.image_interior] at inside
  obtain ⟨p, member, rfl⟩ := inside
  have cut : Cap.horizontal ((family (T.support f)).place
      ((family (T.support f)).project.symm p)) ∈ cuts := on_cut
  rw [(family (T.support f)).horizontal_place, AffineEquiv.apply_symm_apply] at cut
  exact Set.disjoint_left.mp (outside f) member cut

open Classical in
/-- Whole physical face refinement and original geometric cuts derive exact cut seam matching. -/
theorem nestedSubdivision_conforming
    (oldConforming : TriangleFamily.Conforming T.projectedTriangle)
    (conforming : TriangleFamily.Conforming U.projectedTriangle)
    (inside : (interior (clip family W)).Nonempty) (cover : T.FaceRefinement U)
    (nonempty : (clip family Z).Nonempty) (cuts : Set Plane) (closed : IsClosed cuts)
    (outside : ∀ f, Disjoint (interior (T.projectedTriangle f).carrier) cuts)
    (retain : Set T.pairedComplex.Seam)
    (removed : ∀ s, s ∉ retain →
      ∀ x : (T.pairedComplex.triangle (T.pairedComplex.left s).face).Edge
        (T.pairedComplex.left s).edge,
      T.pairedFolding.place (T.pairedComplex.left s).face x.val ∈ Cap.horizontal ⁻¹' cuts)
    (kept : ∀ s ∈ retain,
      Disjoint (T.pairedFolding.openSeamImage s) (Cap.horizontal ⁻¹' cuts))
    (aligned : ∀ f e (x : (U.projectedTriangle f).Edge e),
      ¬ (U.projectedTriangle f).IsVertex x.val → x.val ∈ cuts →
        (U.projectedTriangle f).edge e ⊆ cuts) :
    (T.nestedSubdivision U cover).Conforming retain (T.nestedRetain U cuts) := by
  apply (T.nestedSubdivision U cover).conforming_of_physicalCuts
    T.pairedFolding (T.nestedFolding U) (T.nestedSubdivision_spatial U cover)
    (Cap.horizontal ⁻¹' cuts) (closed.preimage Cap.horizontalCLM.continuous)
    (T.physical_cut_disjoint_face_interior cuts outside) ?_
    (T.nestedFolding_embedded U conforming inside cover nonempty) retain (T.nestedRetain U cuts)
    removed kept (T.nested_removed_edge U cuts) (T.nested_retained_open_edge U cuts aligned)
  intro x y same
  apply T.pairedProjection_injective oldConforming
  exact congrArg Cap.horizontal same

end Unfoldings.SpatialEnvelope.Triangulation
