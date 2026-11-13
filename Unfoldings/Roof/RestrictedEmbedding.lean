module

public import Unfoldings.Roof.ProjectedSeamCompletion
public import Unfoldings.Roof.RestrictedBoundaryFrontier
public import Unfoldings.Complex.FaceRestrictionPairings
public import Unfoldings.Complex.ProjectedJordanEmbedding

/-! A Jordan whole-face roof patch has injective projection on its actual intrinsic surface. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
/-- A whole-face roof restriction whose geometric frontier is Jordan has no intrinsic vertex
pinches: its actual planar projection is injective on all closed face points. -/
theorem restrictProjection_injective_of_Jordan (U : Set Face) (nonempty : U.Nonempty)
    (jordan : Schoenflies.IsJordanCurve (frontier (K.restrictedCarrier U))) :
    Function.Injective (K.restrictProjection U) := by
  let R := C.restrictFaces U
  let A := fun f : {f : Face // f ∈ U} => K.projectFaceEquiv f.val
  have projected (f : {f : Face // f ∈ U}) :
      R.affineProjectedTriangle A f = K.projectedTriangle f.val := rfl
  have joined : ∀ s x, A (R.left s).face x.val =
      A (R.right s).face (R.identify s x).val :=
    fun s x => K.projectedTriangle_joined s.val x
  have conforming : TriangleFamily.Conforming (R.affineProjectedTriangle A) := by
    intro f g different p member
    exact K.projectedTriangles_conforming f.val g.val
      (fun same => different (Subtype.ext same)) p member
  have separated : Pairwise (fun f g => Disjoint
      (interior (R.affineProjectedTriangle A f).carrier)
      (interior (R.affineProjectedTriangle A g).carrier)) := by
    intro f g different
    exact K.projectedTriangles_nonoverlapping (fun same => different (Subtype.ext same))
  have complete : ∀ f g : {f : Face // f ∈ U}, f ≠ g → ∀ e d : Fin 3,
      (R.affineProjectedTriangle A f).edge e = (R.affineProjectedTriangle A g).edge d →
        ∃ s, (R.left s = ⟨f, e⟩ ∧ R.right s = ⟨g, d⟩) ∨
          (R.left s = ⟨g, d⟩ ∧ R.right s = ⟨f, e⟩) := by
    intro f g different e d same
    obtain ⟨s, ⟨left, right⟩ | ⟨right, left⟩⟩ :=
      K.exists_seam_of_projected_shared_edge
        (a := ⟨f.val, e⟩) (b := ⟨g.val, d⟩)
        (fun same => different (Subtype.ext same)) same
    · obtain ⟨t, first, last⟩ := C.exists_restricted_seam_of_names U f g e d s left right
      exact ⟨t, Or.inl ⟨first, last⟩⟩
    · obtain ⟨t, first, last⟩ := C.exists_restricted_seam_of_names U g f d e s right left
      exact ⟨t, Or.inr ⟨first, last⟩⟩
  obtain ⟨f, hf⟩ := nonempty
  have inside : (interior (K.restrictedCarrier U)).Nonempty :=
    (K.projectedTriangle f).interior_nonempty.mono
      (interior_mono (Set.subset_iUnion (fun f : {f : Face // f ∈ U} =>
        (K.projectedTriangle f.val).carrier) ⟨f, hf⟩))
  obtain ⟨h, image⟩ := PlanarTopology.exists_ambientDiskHomeomorph
    (K.compact_restrictedCarrier U) inside jordan
  intro x y same
  obtain ⟨a, rfl⟩ := MetricGluing.point_surjective R.Cell (R.glue Set.univ) x
  obtain ⟨b, rfl⟩ := MetricGluing.point_surjective R.Cell (R.glue Set.univ) y
  exact (R.point_eq_iff Set.univ a b).mpr
    (R.related_of_affine_projection_eq_of_ambientDisk A joined h image conforming separated
      complete a b same)

end Unfoldings.ConvexRoof
