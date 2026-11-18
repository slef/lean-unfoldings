module

public import Unfoldings.Roof.NestedFacePatch
public import Unfoldings.Geometry.SpatialEnvelopeOpenSeams

/-! Actual physical cuts on the complete old-face subcomplex of a larger roof mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z W : ℝ} (T : Triangulation family Z) (U : Triangulation family W)

local instance nestedCutOldFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite
local instance nestedCutNewFintype : Fintype U.Index := @Fintype.ofFinite _ U.finite

open Classical in
/-- All original physical pieces with their inherited spatial placements. -/
def nestedFolding : SpatialFolding (T.nestedComplex U) :=
  U.pairedFolding.restrictFaces (T.nestedPieceSet U)

open Classical in
theorem nestedSubdivision_spatial (cover : T.FaceRefinement U)
    (i : T.nestedPieceSet U) (x : Plane) :
    T.pairedFolding.place ((T.nestedSubdivision U cover).parent i)
      ((T.nestedSubdivision U cover).place i x) = (T.nestedFolding U).place i x :=
  T.nestedCoordinates_spatial U i.val (T.nestedParent U i) (T.nestedParent_contains U i) x

variable (conforming : TriangleFamily.Conforming U.projectedTriangle)
  (inside : (interior (clip family W)).Nonempty)

open Classical in
theorem nested_projectedCarrier (cover : T.FaceRefinement U) :
    (U.roof conforming inside).restrictedCarrier (T.nestedPieceSet U) = clip family Z := by
  ext p
  constructor
  · rintro member
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp member
    rw [U.roof_projectedTriangle] at member
    exact T.cover.symm.subset (Set.mem_iUnion.mpr
      ⟨T.nestedParent U i, T.nestedParent_contains U i member⟩)
  · intro member
    obtain ⟨f, member⟩ := Set.mem_iUnion.mp (T.cover.subset member)
    obtain ⟨i, contained, member⟩ := cover f p member
    exact Set.mem_iUnion.mpr ⟨⟨i, f, contained⟩, by rwa [U.roof_projectedTriangle]⟩

include conforming inside in
open Classical in
/-- A complete old-footprint patch has no intrinsic pinches in its inherited new mesh. -/
theorem nestedFolding_embedded (cover : T.FaceRefinement U)
    (nonempty : (clip family Z).Nonempty) : (T.nestedFolding U).IsEmbedded := by
  obtain ⟨p, member⟩ := nonempty
  obtain ⟨f, member⟩ := Set.mem_iUnion.mp (T.cover.subset member)
  obtain ⟨i, contained, _⟩ := cover f p member
  have selected : (T.nestedPieceSet U).Nonempty := ⟨i, f, contained⟩
  have injective := (U.roof conforming inside).restrictProjection_injective_of_convex
    (T.nestedPieceSet U) selected (by
      rw [T.nested_projectedCarrier U conforming inside cover]
      exact AffineEnvelope.convex_clip _ Z)
  intro x y same
  apply injective
  exact congrArg Cap.horizontal same

open Classical in
/-- Keep precisely the inherited new seams outside the original geometric cut set. -/
def nestedRetain (cuts : Set Plane) : Set (T.nestedComplex U).Seam :=
  U.pairedComplex.restrictRetain (T.nestedPieceSet U) (U.retainOutside cuts)

open Classical in
theorem nested_removed_edge (cuts : Set Plane) (s : (T.nestedComplex U).Seam)
    (removed : s ∉ T.nestedRetain U cuts)
    (x : ((T.nestedComplex U).triangle ((T.nestedComplex U).left s).face).Edge
      ((T.nestedComplex U).left s).edge) :
    (T.nestedFolding U).place ((T.nestedComplex U).left s).face x.val ∈
      Cap.horizontal ⁻¹' cuts := U.removed_edge_mem_cut cuts s.val removed x

open Classical in
theorem nested_retained_open_edge (cuts : Set Plane)
    (aligned : ∀ f e (x : (U.projectedTriangle f).Edge e),
      ¬ (U.projectedTriangle f).IsVertex x.val → x.val ∈ cuts →
        (U.projectedTriangle f).edge e ⊆ cuts)
    (s : (T.nestedComplex U).Seam) (kept : s ∈ T.nestedRetain U cuts) :
    Disjoint ((T.nestedFolding U).openSeamImage s) (Cap.horizontal ⁻¹' cuts) :=
  U.retained_openSeamImage_disjoint cuts aligned s.val kept

end Unfoldings.SpatialEnvelope.Triangulation
