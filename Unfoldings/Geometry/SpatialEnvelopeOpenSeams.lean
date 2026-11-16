module

public import Unfoldings.Geometry.SpatialEnvelopePhysicalCut
public import Unfoldings.Geometry.SpatialEnvelopeCuts
public import Unfoldings.Geometry.EdgeParameters

/-! Geometric whole-edge alignment determines the actual physical retained attachments. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

/-- An open edge contains no original triangle vertex. -/
theorem not_isVertex_of_mem_openSegment (T : Triangle) (e : Fin 3) {p : Plane}
    (inside : p ∈ openSegment ℝ (T.vertex e) (T.vertex (next e))) : ¬ T.IsVertex p := by
  have member : p ∈ AffineMap.lineMap (T.vertex e) (T.vertex (next e)) '' Set.Ioo (0 : ℝ) 1 :=
    Eq.mp (congrArg (fun a : Set Plane => p ∈ a)
      (openSegment_eq_image_lineMap ℝ (T.vertex e) (T.vertex (next e)))) inside
  obtain ⟨t, ht, rfl⟩ := member
  exact T.lineMap_edge_not_vertex e ht

end Unfoldings.Triangle
namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
  (T : Triangulation family Z)

local instance openSeamIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- The actual open seam projects onto its original open projected edge. -/
theorem horizontal_openSeamImage (s : T.pairedComplex.Seam) :
    Cap.horizontal '' T.pairedFolding.openSeamImage s =
      openSegment ℝ
        ((T.projectedTriangle (T.pairedComplex.left s).face).vertex (T.pairedComplex.left s).edge)
        ((T.projectedTriangle (T.pairedComplex.left s).face).vertex
          (Triangle.next (T.pairedComplex.left s).edge)) := by
  change Cap.horizontal '' openSegment ℝ
    ((T.pairedFolding.place (T.pairedComplex.left s).face)
      ((T.pairedComplex.triangle (T.pairedComplex.left s).face).vertex
        (T.pairedComplex.left s).edge))
    ((T.pairedFolding.place (T.pairedComplex.left s).face)
      ((T.pairedComplex.triangle (T.pairedComplex.left s).face).vertex
        (Triangle.next (T.pairedComplex.left s).edge))) = _
  refine (image_openSegment ℝ Cap.horizontal.toAffineMap _ _).trans ?_
  congr 1 <;>
    exact ((family (T.support (T.pairedComplex.left s).face)).horizontal_place _).trans
      ((family (T.support (T.pairedComplex.left s).face)).project.apply_symm_apply _)

/-- Closed original edges omitted by `retainOutside` lie in the actual physical cut. -/
theorem removed_edge_mem_cut (cuts : Set Plane) (s : T.pairedComplex.Seam)
    (removed : s ∉ T.retainOutside cuts)
    (x : (T.pairedComplex.triangle (T.pairedComplex.left s).face).Edge
      (T.pairedComplex.left s).edge) :
    Cap.horizontal (T.placement (T.pairedComplex.left s).face x.val) ∈ cuts := by
  have selected : (T.projectedTriangle (T.pairedComplex.left s).face).edge
      (T.pairedComplex.left s).edge ⊆ cuts := not_not.mp removed
  exact selected (by
    change Cap.horizontal ((family (T.support (T.pairedComplex.left s).face)).place x.val) ∈ _
    rw [(family (T.support (T.pairedComplex.left s).face)).horizontal_place]
    exact (T.edgeProjection (T.pairedComplex.left s).face (T.pairedComplex.left s).edge x).property)

/-- If touching a cut at a nonvertex edge point forces the whole edge into the cut,
then every retained open physical seam avoids it. This is a geometric condition only. -/
theorem retained_openSeamImage_disjoint (cuts : Set Plane)
    (aligned : ∀ f e (x : (T.projectedTriangle f).Edge e),
      ¬ (T.projectedTriangle f).IsVertex x.val → x.val ∈ cuts →
        (T.projectedTriangle f).edge e ⊆ cuts)
    (s : T.pairedComplex.Seam) (kept : s ∈ T.retainOutside cuts) :
    Disjoint (T.pairedFolding.openSeamImage s) (Cap.horizontal ⁻¹' cuts) := by
  apply Set.disjoint_left.mpr
  intro z inside member
  have projected := (T.horizontal_openSeamImage s).subset ⟨z, inside, rfl⟩
  exact kept (aligned (T.pairedComplex.left s).face (T.pairedComplex.left s).edge
    ⟨Cap.horizontal z, openSegment_subset_segment ℝ _ _ projected⟩
    ((T.projectedTriangle (T.pairedComplex.left s).face).not_isVertex_of_mem_openSegment
      (T.pairedComplex.left s).edge projected) member)

/-- Aligned whole-edge cuts have exactly the original retained triangle metric. -/
def alignedCutGraphEquiv (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (cuts : Set Plane)
    (aligned : ∀ f e (x : (T.projectedTriangle f).Edge e),
      ¬ (T.projectedTriangle f).IsVertex x.val → x.val ∈ cuts →
        (T.projectedTriangle f).edge e ⊆ cuts) :
    T.pairedComplex.Realization (T.retainOutside cuts) ≃ᵢ T.graphPartition.Cut cuts :=
  T.pairedCutGraphEquiv conforming (T.retainOutside cuts) cuts
    (T.removed_edge_mem_cut cuts) (T.retained_openSeamImage_disjoint cuts aligned)

end Unfoldings.SpatialEnvelope.Triangulation
