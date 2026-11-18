module

public import Unfoldings.Roof.CompletionFacePatch
public import Unfoldings.Development.AffineProjectionEmbedding

/-! The actual projected metric on each physical completion patch embeds in its old triangle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations) (f : Face)

local instance completionProjectedFacePatchIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
def facePieceProjection (i : E.facePieceSet f) : Plane ≃ᵃ[ℝ] Plane :=
  ((K.completionPlanes E.tentHeight (Real.sin φ / 2)) (E.partition.support i.val)).project

open Classical in
theorem facePieceProjection_joined (s : (E.facePieceComplex f).Seam)
    (x : ((E.facePieceComplex f).triangle ((E.facePieceComplex f).left s).face).Edge
      ((E.facePieceComplex f).left s).edge) :
    E.facePieceProjection f ((E.facePieceComplex f).left s).face x.val =
      E.facePieceProjection f ((E.facePieceComplex f).right s).face
        ((E.facePieceComplex f).identify s x).val :=
  (E.partition.paired_seam_projection s.val x).symm

open Classical in
theorem facePieceProjection_triangle (i : E.facePieceSet f) :
    (E.facePieceComplex f).affineProjectedTriangle (E.facePieceProjection f) i =
      E.partition.projectedTriangle i.val :=
  E.partition.affineProjectedTriangle_eq i.val

open Classical in
theorem facePieceProjection_separated : Pairwise (fun i j : E.facePieceSet f =>
    Disjoint (interior ((E.facePieceComplex f).affineProjectedTriangle
      (E.facePieceProjection f) i).carrier)
      (interior ((E.facePieceComplex f).affineProjectedTriangle
        (E.facePieceProjection f) j).carrier)) := by
  intro i j different
  rw [E.facePieceProjection_triangle f i, E.facePieceProjection_triangle f j]
  exact E.partition.separated (fun same => different (Subtype.ext same))

open Classical in
def facePieceProjectedComplex := (E.facePieceComplex f).affineProjectionComplex
  (E.facePieceProjection f) (E.facePieceProjection_joined f)

open Classical in
def facePieceProjectedDevelopment :
    FacewiseDevelopment (E.facePieceProjectedComplex f) Set.univ :=
  (E.facePieceComplex f).affineProjectionDevelopment
    (E.facePieceProjection f) (E.facePieceProjection_joined f)
    (E.facePieceProjection_separated f)

open Classical in
theorem facePieceProjectedDevelopment_injective :
    Function.Injective (E.facePieceProjectedDevelopment f).toPlane := by
  apply (E.facePieceComplex f).affineProjectionDevelopment_injective
    (E.facePieceProjection f) (E.facePieceProjection_joined f)
    (E.facePieceProjection_separated f)
  intro a b same
  apply ((E.facePieceComplex f).point_eq_iff Set.univ a b).mp
  apply E.facePieceDevelopment_injective f
  change E.originalPlace a.1.val f a.1.property a.2.val =
    E.originalPlace b.1.val f b.1.property b.2.val
  exact (E.originalPlace_apply a.1.val f a.1.property a.2.val).trans
    ((congrArg (K.projectFaceEquiv f).symm same).trans
      (E.originalPlace_apply b.1.val f b.1.property b.2.val).symm)

open Classical in
theorem facePieceProjectedDevelopment_range :
    Set.range (E.facePieceProjectedDevelopment f).toPlane = (K.projectedTriangle f).carrier := by
  change Set.range ((E.facePieceComplex f).affineProjectionDevelopment
    (E.facePieceProjection f) (E.facePieceProjection_joined f)
    (E.facePieceProjection_separated f)).toPlane = _
  rw [(E.facePieceComplex f).affineProjectionDevelopment_range
    (E.facePieceProjection f) (E.facePieceProjection_joined f)
    (E.facePieceProjection_separated f)]
  simp_rw [E.facePieceProjection_triangle f]
  ext p
  constructor
  · intro member
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp member
    exact i.property member
  · intro member
    obtain ⟨i, contained, member⟩ := E.original_face_covered_by_contained_pieces f p member
    exact Set.mem_iUnion.mpr ⟨⟨i, contained⟩, member⟩

end Unfoldings.ConvexRoof.CompletionMesh
