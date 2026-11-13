module

public import Unfoldings.Roof.SpatialEnvelopeCap
public import Unfoldings.Cap.ProjectedFaces
public import Unfoldings.Cap.NormalImage

/-! Exact projected coordinates of the normalized physical affine-roof mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z : ℝ} (T : Triangulation family Z)

local instance spatialCoordinatesIndexFintype : Fintype T.Index :=
  @Fintype.ofFinite _ T.finite

theorem normalizedCap_projectFace (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (inside : (interior (clip family Z)).Nonempty) (i : T.Index) (x : Plane) :
    (T.normalizedCap conforming inside).projectFace i x = (family (T.support i)).project x := by
  change Cap.horizontal (T.placement i x + Cap.horizontalAtHeight 0 (-Z)) = _
  rw [ConvexRoof.horizontal_add_level]
  exact (family (T.support i)).horizontal_place x

theorem normalizedCap_projectedTriangle_vertex
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (inside : (interior (clip family Z)).Nonempty) (i : T.Index) (k : Fin 3) :
    ((T.normalizedCap conforming inside).projectedTriangle i).vertex k =
      (T.projectedTriangle i).vertex k := by
  rw [ConvexCap.projectedTriangle_vertex]
  change (T.normalizedCap conforming inside).projectFace i ((T.triangle i).vertex k) = _
  rw [T.normalizedCap_projectFace conforming inside]
  exact (family (T.support i)).project.apply_symm_apply _

theorem normalizedCap_projectedTriangle_carrier
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (inside : (interior (clip family Z)).Nonempty) (i : T.Index) :
    ((T.normalizedCap conforming inside).projectedTriangle i).carrier =
      (T.projectedTriangle i).carrier :=
  congrArg (fun vertex : Fin 3 → Plane => convexHull ℝ (Set.range vertex))
    (funext (T.normalizedCap_projectedTriangle_vertex conforming inside i))

theorem normalizedCap_projectedTriangle_edge
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (inside : (interior (clip family Z)).Nonempty) (i : T.Index) (e : Fin 3) :
    ((T.normalizedCap conforming inside).projectedTriangle i).edge e =
      (T.projectedTriangle i).edge e :=
  congrArg₂ (segment ℝ) (T.normalizedCap_projectedTriangle_vertex conforming inside i e)
    (T.normalizedCap_projectedTriangle_vertex conforming inside i (Triangle.next e))

theorem normalizedCap_normalSlope (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (inside : (interior (clip family Z)).Nonempty) (i : T.Index) :
    (T.normalizedCap conforming inside).normalSlope i =
      ((family (T.support i)).normal 2)⁻¹ • Cap.horizontal (family (T.support i)).normal := rfl

end Unfoldings.SpatialEnvelope.Triangulation
