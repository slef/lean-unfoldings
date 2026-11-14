module

public import Unfoldings.Cap.JordanFaceSelection
public import Unfoldings.Topology.IncidentCellNeighborhood

/-! Bound the actual Jordan-boundary corner excess by the cap's total intrinsic curvature. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan avoids

theorem jordanFace_subset_domain (f : Face) (member : f ∈ K.jordanFaces J) :
    (K.projectedTriangle f).carrier ⊆ PlanarTopology.closedJordanDomain J := by
  apply ConvexCellRegion.cell_subset_of_selected _ _ f isClosed_closure
    (K.projectedTriangle f).compact_carrier.isClosed (K.projectedTriangle f).convex_carrier
    (K.projectedTriangle f).interior_nonempty _ member
  change Disjoint (interior (K.projectedTriangle f).carrier)
    (frontier (PlanarTopology.closedJordanDomain J))
  rw [PlanarTopology.frontier_closedJordanDomain jordan]
  exact avoids f

theorem jordanFaces_not_fullStar_on_boundary (contains : J ⊆ interior K.footprint)
    (w : C.Vertex Set.univ) (boundary : K.projectedVertex w ∈ J) :
    ¬ C.FullStarIn (K.jordanFaces J) w := by
  intro full
  have incident (f : Face) (present : K.projectedVertex w ∈ (K.projectedTriangle f).carrier) :
      (K.projectedTriangle f).carrier ⊆ PlanarTopology.closedJordanDomain J := by
    obtain ⟨i, corner⟩ := K.projected_corner_of_vertex_mem w f present
    have same : C.vertexOfCorner Set.univ (f, i) = w :=
      K.projectedVertex_injective ((K.projectedVertex_ofCorner f i).trans corner)
    exact K.jordanFace_subset_domain jordan avoids f (full (f, i) same)
  have inside := interior_of_incident_closed_cells (fun f => (K.projectedTriangle f).carrier)
    (fun f => (K.projectedTriangle f).compact_carrier.isClosed)
    K.footprint_eq_union_projectedTriangles.subset (contains boundary) incident
  have frontier : K.projectedVertex w ∈ frontier (PlanarTopology.closedJordanDomain J) :=
    (PlanarTopology.frontier_closedJordanDomain jordan).symm ▸ boundary
  exact Set.disjoint_left.mp disjoint_interior_frontier inside frontier

theorem jordanFaces_excess_zero_outside (w : C.Vertex Set.univ)
    (outside : K.projectedVertex w ∉ PlanarTopology.closedJordanDomain J) :
    K.regionalAngleExcess (K.jordanFaces J) w = 0 := by
  classical
  unfold regionalAngleExcess TriangleComplex.regionalCornerSum
  apply Finset.sum_eq_zero
  intro c _
  have excluded : ¬ (c.1 ∈ K.jordanFaces J ∧ C.vertexOfCorner Set.univ c = w) := by
    rintro ⟨selected, same⟩
    apply outside
    apply K.jordanFace_subset_domain jordan avoids c.1 selected
    rw [← same, K.projectedVertex_ofCorner]
    exact (K.projectedTriangle c.1).vertex_mem c.2
  simp only [excluded, ite_false]

open scoped Classical in
/-- The abstract partial-star sum is exactly the sum along the actual geometric Jordan curve. -/
theorem partialStar_sum_eq_jordan_boundary (contains : J ⊆ interior K.footprint) :
    (∑ w : C.Vertex Set.univ,
      if ¬ C.FullStarIn (K.jordanFaces J) w then K.regionalAngleExcess (K.jordanFaces J) w else 0) =
        ∑ w : C.Vertex Set.univ,
          if K.projectedVertex w ∈ J then K.regionalAngleExcess (K.jordanFaces J) w else 0 := by
  classical
  have terms (w : C.Vertex Set.univ) :
      (if ¬ C.FullStarIn (K.jordanFaces J) w then
        K.regionalAngleExcess (K.jordanFaces J) w else 0) =
        (if K.projectedVertex w ∈ J then K.regionalAngleExcess (K.jordanFaces J) w else 0) := by
    by_cases boundary : K.projectedVertex w ∈ J
    · simp [K.jordanFaces_not_fullStar_on_boundary jordan avoids contains w boundary, boundary]
    · by_cases member : K.projectedVertex w ∈ PlanarTopology.closedJordanDomain J
      · have inside : K.projectedVertex w ∈ interior (PlanarTopology.closedJordanDomain J) := by
          by_contra outside
          have frontier : K.projectedVertex w ∈ frontier (PlanarTopology.closedJordanDomain J) :=
            ⟨subset_closure member, outside⟩
          exact boundary ((PlanarTopology.frontier_closedJordanDomain jordan).subset frontier)
        simp [K.jordanFaces_fullStar_of_interior w inside, boundary]
      · rw [K.jordanFaces_excess_zero_outside jordan avoids w member]
        simp
  exact Finset.sum_congr rfl (fun w _ => terms w)

open scoped Classical in
/-- Actual selected face fans on the geometric Jordan curve satisfy the curvature budget. -/
theorem abs_jordan_boundary_angle_excess_le (contains : J ⊆ interior K.footprint) :
    |∑ w : C.Vertex Set.univ,
      if K.projectedVertex w ∈ J then K.regionalAngleExcess (K.jordanFaces J) w else 0| ≤
        C.totalInteriorAngularDefect Set.univ := by
  rw [← K.partialStar_sum_eq_jordan_boundary jordan avoids contains]
  exact K.abs_regional_partialStar_excess_le (K.jordanFaces J)

end Unfoldings.ConvexCap
