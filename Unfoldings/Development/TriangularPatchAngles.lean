module

public import Unfoldings.Development.FlatCap
public import Unfoldings.Cap.TriangularFootprintAngles
public import Unfoldings.Cap.TriangularFootprintStraightAngles
public import Unfoldings.Geometry.TriangleSubsetCorners

/-! In an embedded triangular patch, angle sums depend only on the actual footprint. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (D : FacewiseDevelopment C Set.univ) (embedded : Function.Injective D.toPlane)
  (T : Triangle) (domain : Set.range D.toPlane = T.carrier)

include domain in
private theorem convex_footprint : Convex ℝ (Set.range D.toPlane) :=
  domain.symm ▸ T.convex_carrier

include domain in
private theorem interior_footprint : (interior (Set.range D.toPlane)).Nonempty :=
  domain.symm ▸ T.interior_nonempty

include embedded in
open Classical in
private theorem sum_cornerAngle_at_pos_eq_totalAngle (w : C.Vertex Set.univ) {x : Plane}
    (position : D.toPlane (C.vertexPoint Set.univ w) = x) :
    (∑ c : C.Corner, if D.place c.1 ((C.triangle c.1).vertex c.2) = x then
      (C.triangle c.1).cornerAngle c.2 else 0) = C.totalAngle Set.univ w := by
  unfold TriangleComplex.totalAngle
  apply Finset.sum_congr rfl
  intro c _
  have same : D.place c.1 ((C.triangle c.1).vertex c.2) = x ↔ C.vertexOfCorner Set.univ c = w := by
    constructor
    · intro equal
      apply C.vertexPoint_injective Set.univ
      apply embedded
      exact equal.trans position.symm
    · intro equal
      exact (congrArg (fun v => D.toPlane (C.vertexPoint Set.univ v)) equal).trans position
  by_cases at_w : C.vertexOfCorner Set.univ c = w
  · rw [ite_eq_left at_w, ite_eq_left (same.mpr at_w)]
  · rw [ite_eq_right at_w, ite_eq_right (mt same.mp at_w)]

include domain in
/-- The original apex of an embedded triangular patch is an actual fine vertex. -/
theorem exists_vertex_of_triangular_patch_corner (i : Fin 3) :
    ∃ w : C.Vertex Set.univ, D.toPlane (C.vertexPoint Set.univ w) = T.vertex i := by
  obtain ⟨x, at_corner⟩ := domain.symm.subset (T.vertex_mem i)
  obtain ⟨⟨j, y⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) x
  have contained : (D.placedTriangle j).carrier ⊆ T.carrier := by
    rw [D.placedTriangle_carrier]
    rintro z ⟨q, hq, rfl⟩
    exact domain.subset ⟨C.faceMap Set.univ j ⟨q, hq⟩, rfl⟩
  have member : T.vertex i ∈ (D.placedTriangle j).carrier := by
    rw [D.placedTriangle_carrier]
    exact ⟨y.val, y.property, at_corner⟩
  obtain ⟨k, equal⟩ := (D.placedTriangle j).isVertex_of_contained_corner T contained i member
  exact ⟨C.vertexOfCorner Set.univ (j, k), equal⟩

include domain embedded in
open Classical in
/-- Group the fine corner angles at a coarse corner in the actual affine chart. -/
theorem sum_cornerAngles_at_triangular_patch_corner (i : Fin 3) :
    (∑ c : C.Corner, if D.place c.1 ((C.triangle c.1).vertex c.2) = T.vertex i then
      (C.triangle c.1).cornerAngle c.2 else 0) = T.cornerAngle i := by
  let K := D.flatCap embedded (D.convex_footprint T domain) (D.interior_footprint T domain)
  have footprint : K.footprint = T.carrier := (D.flatCap_footprint _ _ _).trans domain
  obtain ⟨w, at_corner⟩ := D.exists_vertex_of_triangular_patch_corner T domain i
  rw [D.sum_cornerAngle_at_pos_eq_totalAngle embedded w at_corner,
    ← D.flatCap_projectedTotalAngle embedded (D.convex_footprint T domain)
      (D.interior_footprint T domain) Set.univ w]
  exact K.projectedTotalAngle_eq_triangle_corner T footprint w i
    ((D.horizontalFolding_projection _).trans at_corner)

include domain embedded in
open Classical in
/-- A fine vertex on the interior of an old edge has angle sum exactly π in that patch. -/
theorem sum_cornerAngles_at_triangular_patch_edge (w : C.Vertex Set.univ) {x : Plane}
    (position : D.toPlane (C.vertexPoint Set.univ w) = x) (boundary : x ∈ frontier T.carrier)
    (regular : ¬ T.IsVertex x) :
    (∑ c : C.Corner, if D.place c.1 ((C.triangle c.1).vertex c.2) = x then
      (C.triangle c.1).cornerAngle c.2 else 0) = Real.pi := by
  let K := D.flatCap embedded (D.convex_footprint T domain) (D.interior_footprint T domain)
  have footprint : K.footprint = T.carrier := (D.flatCap_footprint _ _ _).trans domain
  rw [D.sum_cornerAngle_at_pos_eq_totalAngle embedded w position,
    ← D.flatCap_projectedTotalAngle embedded (D.convex_footprint T domain)
      (D.interior_footprint T domain) Set.univ w]
  have at_x : K.projectedVertex w = x := (D.horizontalFolding_projection _).trans position
  exact K.projectedTotalAngle_eq_pi_of_triangle_boundary T footprint w
    (at_x.symm ▸ boundary) (at_x.symm ▸ regular)

end Unfoldings.FacewiseDevelopment
