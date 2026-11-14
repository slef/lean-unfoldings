module

public import Unfoldings.Roof.SpatialEnvelopeRoof
public import Unfoldings.Roof.ProjectedFaces

/-! The physical mesh roof has exactly its prescribed projected triangles and footprint. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z : ℝ} (T : Triangulation family Z)

local instance spatialEnvelopeProjectionIndexFintype : Fintype T.Index :=
  @Fintype.ofFinite _ T.finite

variable (conforming : TriangleFamily.Conforming T.projectedTriangle)
  (inside : (interior (clip family Z)).Nonempty)

theorem roof_projectFace (i : T.Index) (x : Plane) :
    (T.roof conforming inside).projectFace i x = (family (T.support i)).project x :=
  (family (T.support i)).horizontal_place x

theorem roof_projectedTriangle (i : T.Index) :
    (T.roof conforming inside).projectedTriangle i = T.projectedTriangle i := by
  apply Triangle.eq_of_vertex_eq
  intro k
  rw [ConvexRoof.projectedTriangle_vertex]
  change (T.roof conforming inside).projectFace i ((T.triangle i).vertex k) = _
  rw [T.roof_projectFace conforming inside]
  exact (family (T.support i)).project.apply_symm_apply _

theorem roof_footprint : (T.roof conforming inside).footprint = clip family Z :=
  T.pairedFolding_footprint

end Unfoldings.SpatialEnvelope.Triangulation
