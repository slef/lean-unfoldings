module

public import Unfoldings.Roof.CompletionSubdivisionAngles
public import Unfoldings.Roof.ProjectedBankMetric
public import Unfoldings.Complex.AffineProjectionSubdivision
public import Unfoldings.Development.AffineProjectionEmbedding

/-! Physical completion pieces form the same conforming subdivision in the projected metric. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionProjectedSubdivisionIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
def originalProjection (g : E.originalPieceSet) : Plane ≃ᵃ[ℝ] Plane :=
  ((K.completionPlanes E.tentHeight (Real.sin φ / 2)) (E.partition.support g.val)).project

open Classical in
theorem originalProjection_joined (s : E.originalComplex.Seam)
    (x : (E.originalComplex.triangle (E.originalComplex.left s).face).Edge
      (E.originalComplex.left s).edge) :
    E.originalProjection (E.originalComplex.left s).face x.val =
      E.originalProjection (E.originalComplex.right s).face (E.originalComplex.identify s x).val :=
  (E.partition.paired_seam_projection s.val x).symm

open Classical in
theorem originalSubdivision_projection (g : E.originalPieceSet) (x : Plane) :
    K.projectFaceEquiv (E.originalSubdivision.parent g) (E.originalSubdivision.place g x) =
      E.originalProjection g x :=
  E.originalPlace_projection g.val (E.originalParent g) (E.originalParent_contains g) x

open Classical in
def originalProjectedComplex := E.originalComplex.affineProjectionComplex
  E.originalProjection E.originalProjection_joined

open Classical in
def originalProjectedSubdivision : K.projectedMetricComplex.Subdivision
    E.originalProjectedComplex :=
  E.originalSubdivision.affineProjectionSubdivision
    K.projectFaceEquiv K.projectedTriangle_joined
    E.originalProjection E.originalProjection_joined E.originalSubdivision_projection

open Classical in
theorem originalProjectedSubdivision_conforming (retain : Set C.Seam) :
    E.originalProjectedSubdivision.Conforming retain (E.originalRetain retain) :=
  E.originalSubdivision.affineProjectionSubdivision_conforming
    K.projectFaceEquiv K.projectedTriangle_joined
    E.originalProjection E.originalProjection_joined E.originalSubdivision_projection
    (E.originalSubdivision_conforming retain)

end Unfoldings.ConvexRoof.CompletionMesh
