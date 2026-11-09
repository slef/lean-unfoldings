module

public import Unfoldings.Polyhedron.Closedness
public import Unfoldings.Complex.RegularEdges
public import Unfoldings.Geometry.TriangleBoundary

/-!
# Every nonvertex point of an actual convex boundary is regular

Uncut edges have derived seam pairings, and spatial rigidity makes their
incident faces distinct. The constructed face and hinge charts therefore
cover every point except the finite original vertex classes.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem isRegularPoint_edge (e : EdgeRef Face)
    (x : (C.triangle e.face).Edge e.edge) (regular : ¬ (C.triangle e.face).IsVertex x) :
    C.IsRegularPoint Set.univ
      (MetricGluing.point C.Cell (C.glue Set.univ) (C.edgePoint e x)) := by
  obtain ⟨s, side, equal⟩ := P.exists_seam_at_edge e
  subst e
  exact C.isRegularPoint_seamSide Set.univ s (Set.mem_univ s) (F.incident_faces_ne s) side x regular

theorem isRegularPoint_of_not_vertex (x : C.Realization Set.univ)
    (nonvertex : ∀ v, x ≠ C.vertexPoint Set.univ v) : C.IsRegularPoint Set.univ x := by
  obtain ⟨a, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) x
  have regular : ¬ C.IsVertex a := by
    intro vertex
    obtain ⟨v, equal⟩ := (C.mem_range_vertexPoint_iff Set.univ a).mpr vertex
    exact nonvertex v equal.symm
  obtain ⟨face, p⟩ := a
  by_cases inside : p.val ∈ interior (C.triangle face).carrier
  · exact C.isRegularPoint_face Set.univ face p inside
  · obtain ⟨e, member⟩ := (C.triangle face).exists_edge_of_not_mem_interior p inside
    exact P.isRegularPoint_edge ⟨face, e⟩ ⟨p.val, member⟩ regular

end Unfoldings.SpatialFolding.ConvexBoundary
