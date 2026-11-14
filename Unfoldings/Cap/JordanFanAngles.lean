module

public import Unfoldings.Cap.JordanIntrinsicDisk
public import Unfoldings.Complex.FaceRestrictionWeights

/-! Actual intrinsic Jordan vertex fans have exactly the selected original corner contributions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

open Classical in
/-- Every restricted vertex copy projects to its original geometric vertex. -/
theorem projected_includeRestrictedVertex (U : Set Face)
    (w : (C.restrictFaces U).Vertex Set.univ) :
    K.projectedVertex (C.includeRestrictedVertexUniv U w) =
      K.toRoof.restrictProjection U ((C.restrictFaces U).vertexPoint Set.univ w) := by
  refine Quotient.inductionOn w (fun c => ?_)
  rfl

variable {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- The constructed intrinsic Jordan disk has one vertex fan per selected original vertex. -/
theorem jordan_includeRestrictedVertex_injective :
    Function.Injective (C.includeRestrictedVertexUniv (K.jordanFaces J)) := by
  intro x y same
  apply (C.restrictFaces (K.jordanFaces J)).vertexPoint_injective Set.univ
  apply (K.jordanIntrinsicHomeomorph jordan contains avoids).injective
  apply Subtype.ext
  rw [K.jordanIntrinsicHomeomorph_apply, K.jordanIntrinsicHomeomorph_apply]
  rw [← K.projected_includeRestrictedVertex, ← K.projected_includeRestrictedVertex, same]

include jordan contains avoids in
open Classical in
/-- Original corner weights, including projected angles, are retained on the actual fan. -/
theorem jordan_vertex_corner_sum (weight : C.Corner → ℝ)
    (w : (C.restrictFaces (K.jordanFaces J)).Vertex Set.univ) :
    (C.restrictFaces (K.jordanFaces J)).regionalCornerSum Set.univ
      (fun c => weight (c.1.val, c.2)) w =
        C.regionalCornerSum (K.jordanFaces J) weight
          (C.includeRestrictedVertexUniv (K.jordanFaces J) w) := by
  have fiber := C.regionalCornerSum_restricted_vertex_fiber (K.jordanFaces J) weight
    (C.includeRestrictedVertexUniv (K.jordanFaces J) w)
  simpa only [(K.jordan_includeRestrictedVertex_injective jordan contains avoids).eq_iff,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using fiber

include jordan contains avoids in
open Classical in
theorem jordan_vertex_totalAngle
    (w : (C.restrictFaces (K.jordanFaces J)).Vertex Set.univ) :
    (C.restrictFaces (K.jordanFaces J)).totalAngle Set.univ w =
      C.regionalCornerSum (K.jordanFaces J) (fun c => (C.triangle c.1).cornerAngle c.2)
        (C.includeRestrictedVertexUniv (K.jordanFaces J) w) := by
  have fiber := C.totalAngle_restricted_vertex_fiber (K.jordanFaces J)
    (C.includeRestrictedVertexUniv (K.jordanFaces J) w)
  simpa only [(K.jordan_includeRestrictedVertex_injective jordan contains avoids).eq_iff,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using fiber

end Unfoldings.ConvexCap
