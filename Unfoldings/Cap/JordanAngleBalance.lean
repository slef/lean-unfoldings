module

public import Unfoldings.Cap.JordanRegionalAngles

/-! Relative Gauss–Bonnet for the constructed filling of an interior Jordan curve. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J)
  (contains : J ⊆ interior K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains in
theorem jordanDomain_subset_interior_footprint :
    PlanarTopology.closedJordanDomain J ⊆ interior K.footprint := by
  have compact : IsCompact K.footprint := by
    rw [K.footprint_eq_union_projectedTriangles]
    exact isCompact_iUnion (fun f => (K.projectedTriangle f).compact_carrier)
  exact PlanarTopology.closedJordanDomain_subset_interior jordan
    (PlanarTopology.closedJordanDomain_subset_convex jordan compact K.convex_projection
      (contains.trans interior_subset)) contains

include jordan contains avoids in
theorem jordanFaces_fullStar_iff_interior (w : C.Vertex Set.univ) :
    C.FullStarIn (K.jordanFaces J) w ↔
      K.projectedVertex w ∈ interior (PlanarTopology.closedJordanDomain J) := by
  constructor
  · intro full
    obtain ⟨c, same⟩ := C.vertexOfCorner_surjective Set.univ w
    have selected := full c same
    have member : K.projectedVertex w ∈ PlanarTopology.closedJordanDomain J := by
      apply K.jordanFace_subset_domain jordan avoids c.1 selected
      rw [← same, K.projectedVertex_ofCorner]
      exact (K.projectedTriangle c.1).vertex_mem c.2
    by_contra outside
    have frontier : K.projectedVertex w ∈ frontier (PlanarTopology.closedJordanDomain J) :=
      ⟨subset_closure member, outside⟩
    exact K.jordanFaces_not_fullStar_on_boundary jordan avoids contains w
      ((PlanarTopology.frontier_closedJordanDomain jordan).subset frontier) full
  · exact K.jordanFaces_fullStar_of_interior w

include jordan contains avoids in
open scoped Classical in
/-- The boundary fan excess equals the actual total curvature strictly inside the filling. -/
theorem jordan_boundary_angle_balance :
    (∑ w : C.Vertex Set.univ,
      if K.projectedVertex w ∈ J then K.regionalAngleExcess (K.jordanFaces J) w else 0) =
        ∑ w : C.Vertex Set.univ,
          if K.projectedVertex w ∈ interior (PlanarTopology.closedJordanDomain J) then
            C.interiorAngularDefect Set.univ w else 0 := by
  classical
  rw [← K.partialStar_sum_eq_jordan_boundary jordan avoids contains,
    K.regional_partialStar_balance]
  have rim_zero : (∑ w : C.Vertex Set.univ,
      if C.FullStarIn (K.jordanFaces J) w then K.boundaryAngleExcess w else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    by_cases full : C.FullStarIn (K.jordanFaces J) w
    · have inside := (K.jordanFaces_fullStar_iff_interior jordan contains avoids w).mp full
      have not_boundary := (K.projectedVertex_mem_interior_iff w).mp
        (K.jordanDomain_subset_interior_footprint jordan contains (interior_subset inside))
      simp [full, boundaryAngleExcess, not_boundary]
    · simp [full]
  rw [rim_zero, sub_zero]
  apply Finset.sum_congr rfl
  intro w _
  rw [K.jordanFaces_fullStar_iff_interior jordan contains avoids w]

end Unfoldings.ConvexCap
