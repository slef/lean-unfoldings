module

public import Unfoldings.Cap.ProjectedSeamEndpoints
public import Unfoldings.Geometry.OutwardSegmentNeighbor

/-! Outward local progress chooses an actual incident seam with greater source distance. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- The finite incident-star argument keeps actual edge names and intrinsic endpoints. -/
theorem exists_radially_ascending_seam (retain : Set C.Seam) (q : Plane)
    (v : C.Vertex Set.univ)
    (growth : LocalRadialGrowth
      (⋃ s : {s : C.Seam // s ∉ retain},
        (K.projectedTriangle (C.left s.val).face).edge (C.left s.val).edge)
      q (K.projectedVertex v)) :
    ∃ w s, s ∉ retain ∧ C.seamGraph.IsLink s v w ∧
      dist q (K.projectedVertex v) < dist q (K.projectedVertex w) := by
  let first (s : {s : C.Seam // s ∉ retain}) := K.projectedVertex (C.seamVertex s.val false)
  let last (s : {s : C.Seam // s ∉ retain}) := K.projectedVertex (C.seamVertex s.val true)
  have edge_eq (s : {s : C.Seam // s ∉ retain}) :
      segment ℝ (first s) (last s) =
        (K.projectedTriangle (C.left s.val).face).edge (C.left s.val).edge := rfl
  obtain ⟨s, on_edge, farther⟩ := growth.exists_outward_segment first last
    (by simp only [edge_eq]; exact Set.Subset.rfl)
  obtain ⟨b, at_endpoint⟩ :=
    K.vertex_eq_seamEndpoint_of_projected_edge v s.val ((edge_eq s).subset on_edge)
  cases b
  · refine ⟨C.seamVertex s.val true, s.val, s.property, Or.inl ⟨at_endpoint, rfl⟩, ?_⟩
    rcases farther with impossible | progress
    · exact (lt_irrefl _ (at_endpoint ▸ impossible)).elim
    · exact progress
  · refine ⟨C.seamVertex s.val false, s.val, s.property, Or.inr ⟨at_endpoint, rfl⟩, ?_⟩
    rcases farther with progress | impossible
    · exact progress
    · exact (lt_irrefl _ (at_endpoint ▸ impossible)).elim

end Unfoldings.ConvexCap
