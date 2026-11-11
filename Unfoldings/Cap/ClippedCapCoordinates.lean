module

public import Unfoldings.Cap.ClippedCap

/-! Exact original planar coordinates and support slopes of the normalized physical clip. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.ClipSpatialTriangles

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

local instance clippedCoordinatesIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

theorem normalizedCap_projectedTriangle_vertex
    (conforming : TriangleFamily.Conforming T.projectedTriangle) (lower : Z < 0)
    (i : T.Index) (k : Fin 3) :
    ((T.normalizedCap conforming lower).projectedTriangle i).vertex k =
      (T.projectedTriangle i).vertex k := by
  rw [ConvexCap.projectedTriangle_vertex]
  change Cap.horizontal (T.normalizedFolding.place i ((T.triangle i).vertex k)) = _
  rw [T.normalized_place, horizontal_add_shift]
  change (K.projectFaceEquiv (T.face i))
    ((K.projectFaceEquiv (T.face i)).symm ((T.projectedTriangle i).vertex k)) = _
  exact (K.projectFaceEquiv (T.face i)).apply_symm_apply _

theorem normalizedCap_projectedTriangle_carrier
    (conforming : TriangleFamily.Conforming T.projectedTriangle) (lower : Z < 0)
    (i : T.Index) : ((T.normalizedCap conforming lower).projectedTriangle i).carrier =
      (T.projectedTriangle i).carrier :=
  congrArg (fun vertex : Fin 3 → Plane => convexHull ℝ (Set.range vertex))
    (funext (T.normalizedCap_projectedTriangle_vertex conforming lower i))

theorem normalizedCap_projectedTriangle_edge
    (conforming : TriangleFamily.Conforming T.projectedTriangle) (lower : Z < 0)
    (i : T.Index) (e : Fin 3) : ((T.normalizedCap conforming lower).projectedTriangle i).edge e =
      (T.projectedTriangle i).edge e :=
  congrArg₂ (segment ℝ) (T.normalizedCap_projectedTriangle_vertex conforming lower i e)
    (T.normalizedCap_projectedTriangle_vertex conforming lower i (Triangle.next e))

theorem normalizedCap_normalSlope (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (lower : Z < 0) (i : T.Index) :
    (T.normalizedCap conforming lower).normalSlope i = K.normalSlope (T.face i) := rfl

end Unfoldings.ConvexCap.ClipSpatialTriangles
