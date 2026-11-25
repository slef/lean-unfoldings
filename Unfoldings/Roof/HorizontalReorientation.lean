module

public import Unfoldings.Roof.ProjectedFaces
public import Unfoldings.Roof.VertexProgress
public import Unfoldings.Roof.GradientSelection
public import Unfoldings.Geometry.TriangleAffineEquiv
public import Unfoldings.Cap.HorizontalChartIsometry
public import Unfoldings.Polyhedron.Rotation

/-! Use a bank's own horizontal chart without changing any intrinsic triangle or seam. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

/-- Projecting a horizontally reoriented folding commutes with changing the planar chart. -/
theorem horizontal_rotate_surface (E : Plane ≃ₗᵢ[ℝ] Plane) :
    Cap.horizontal '' (F.rotate (Cap.horizontalChartIsometry E)).surface =
      E '' (Cap.horizontal '' F.surface) := by
  rw [F.rotate_surface, Set.image_image, Set.image_image]
  congr 1
  funext p
  exact Cap.horizontal_horizontalChartIsometry E p

end Unfoldings.SpatialFolding

namespace Unfoldings.ConvexRoof

open Cap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Keep the actual metric roof complex while using a new horizontal isometric chart. -/
def reorient (E : Plane ≃ₗᵢ[ℝ] Plane) : ConvexRoof C where
  folding := K.folding.rotate (horizontalChartIsometry E)
  normal f := horizontalChartIsometry E (K.normal f)
  normal_unit f := ((horizontalChartIsometry E).norm_map _).trans (K.normal_unit f)
  normal_upward f := K.normal_upward f
  normal_tangent f x := by
    let R := horizontalChartIsometry E
    change inner ℝ (R (K.normal f)) (R ((K.folding.place f).linear x)) = 0
    rw [R.inner_map_map, K.normal_tangent]
  supporting f g x := by
    let R := horizontalChartIsometry E
    change inner ℝ (R (K.normal f)) (R (K.folding.place g x.val) - R (K.folding.place f 0)) ≤ 0
    rw [← map_sub, R.inner_map_map]
    exact K.supporting f g x
  projection_injective x y equal := by
    apply K.projection_injective
    apply E.injective
    simpa only [SpatialFolding.rotate_toSpace, horizontal_horizontalChartIsometry] using equal
  convex_projection := by
    rw [K.folding.horizontal_rotate_surface E]
    exact K.convex_projection.linear_image E.toLinearEquiv.toLinearMap
  interior_projection := by
    rw [K.folding.horizontal_rotate_surface E]
    change (interior (E.toHomeomorph '' (horizontal '' K.folding.surface))).Nonempty
    rw [← E.toHomeomorph.image_interior]
    exact K.interior_projection.image _

theorem footprint_reorient (E : Plane ≃ₗᵢ[ℝ] Plane) :
    (K.reorient E).footprint = E '' K.footprint := K.folding.horizontal_rotate_surface E

theorem normalSlope_reorient (E : Plane ≃ₗᵢ[ℝ] Plane) (f : Face) :
    (K.reorient E).normalSlope f = E (K.normalSlope f) := by
  change (K.normal f 2)⁻¹ • horizontal (horizontalChartIsometry E (K.normal f)) = _
  rw [horizontal_horizontalChartIsometry, normalSlope, map_smul]

theorem tiltBound_reorient (E : Plane ≃ₗᵢ[ℝ] Plane) {φ : ℝ} :
    (K.reorient E).TiltBound φ ↔ K.TiltBound φ := Iff.rfl

theorem projectFace_reorient (E : Plane ≃ₗᵢ[ℝ] Plane) (f : Face) (x : Plane) :
    (K.reorient E).projectFace f x = E (K.projectFace f x) :=
  horizontal_horizontalChartIsometry E _

theorem projectedTriangle_reorient (E : Plane ≃ₗᵢ[ℝ] Plane) (f : Face) :
    (K.reorient E).projectedTriangle f =
      (K.projectedTriangle f).affineImage E.toLinearEquiv.toAffineEquiv.toAffineMap
        E.toLinearEquiv.toAffineEquiv.injective := by
  apply Triangle.eq_of_vertex_eq
  intro j
  exact K.projectFace_reorient E f ((C.triangle f).vertex j)

theorem projectedTriangle_reorient_carrier (E : Plane ≃ₗᵢ[ℝ] Plane) (f : Face) :
    ((K.reorient E).projectedTriangle f).carrier = E '' (K.projectedTriangle f).carrier := by
  have carrier (R : ConvexRoof C) :
      (R.projectedTriangle f).carrier = R.projectFace f '' (C.triangle f).carrier :=
    (C.triangle f).affineImage_carrier _ _
  rw [carrier, carrier, Set.image_image]
  congr 1
  funext p
  exact K.projectFace_reorient E f p

theorem projectedVertex_reorient (E : Plane ≃ₗᵢ[ℝ] Plane) (v : C.Vertex Set.univ) :
    (K.reorient E).projectedVertex v = E (K.projectedVertex v) := by
  change horizontal ((K.folding.rotate (horizontalChartIsometry E)).toSpace Set.univ
    (C.vertexPoint Set.univ v)) = _
  rw [SpatialFolding.rotate_toSpace, horizontal_horizontalChartIsometry]
  rfl

end Unfoldings.ConvexRoof
