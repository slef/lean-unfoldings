module

public import Unfoldings.FewestNets.IcosahedronVertexGuard
public import Unfoldings.FewestNets.IcosahedronDualEdges
public import Unfoldings.FewestNets.EndpointCrossingLocality

/-! The local vertex guards imply the global separation hypothesis of the count. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem exists_endpoint_eq_of_near_meshArc {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (o : Orientation ℝ Plane (Fin 2)) (t : MeshFace q) {r : ℝ} (r_lt : r < Real.pi / 2)
    (altitude : ∀ j k : Fin 3, j ≠ k → Real.tan r ≤ cornerGuardAltitude o hq t j k)
    (f : MeshEdge q) {x : Space} (on_f : x ∈ networkEdge (meshEndpoint hq) f)
    (near : angle (facetNormal hq t) x < r) :
    ∃ b : Bool, facetNormal hq t = meshEndpoint hq f b := by
  have wall : x ∈ voronoiWalls (fun s : meshSites q => (s : Space)) := by
    rw [voronoiWalls_eq_meshEdges qbig hq]
    exact Set.mem_iUnion.mpr ⟨f, on_f⟩
  obtain ⟨k, on_g, not_far⟩ := exists_incident_arc_of_near_voronoiWall
    qbig hq o t r_lt altitude wall near
  let g := edgeOpposite hq t k
  let a := oppositeEndpointIndex hq t g
  have near_eq : meshEndpoint hq g (!a) = facetNormal hq t :=
    (meshEndpoint_eq_facetNormal_incidentFace hq g _).trans
      (congrArg (facetNormal hq) (incidentFace_eq_of_incident qbig hq t g
        (edgeOpposite_incident hq t k)))
  have far_eq : meshEndpoint hq g a = facetNormal hq (adjacentFace hq t k) :=
    meshEndpoint_eq_facetNormal_incidentFace hq g a
  by_cases equal : g = f
  · exact ⟨!a, near_eq.symm.trans (congrArg (fun e => meshEndpoint hq e (!a)) equal)⟩
  rw [closedMinorArc_facetNormal_adjacent qbig hq t k] at on_g
  obtain ⟨i, j, hi, hj⟩ := meshEdge_mem_inter_eq_endpoints qbig hq equal on_g on_f
  have flags : i = (!a) ∨ i = a := by cases i <;> cases a <;> decide
  rcases flags with ok | bad
  · rw [ok, near_eq] at hi
    exact ⟨j, hi.symm.trans hj⟩
  · rw [bad, far_eq] at hi
    exact (not_far hi).elim

/-- If every vertex has a local exclusion radius `1.01 * s`, then all nonincident
Voronoi edges are at angular distance at least `s`. -/
theorem meshArcs_separated_of_cornerGuardAltitude {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (o : Orientation ℝ Plane (Fin 2)) {s : ℝ} (spos : 0 < s)
    (s_small : s ≤ icosahedronEdge / q) (r_lt : (101 / 100 : ℝ) * s < Real.pi / 2)
    (altitude : ∀ (t : MeshFace q) (j k : Fin 3), j ≠ k →
      Real.tan ((101 / 100 : ℝ) * s) ≤ cornerGuardAltitude o hq t j k)
    {e f : MeshEdge q} (different : e ≠ f) (no_common : ∀ a b, meshEndpoint hq e a ≠
      meshEndpoint hq f b)
    {x y : Space} (hx : x ∈ networkEdge (meshEndpoint hq) e)
    (hy : y ∈ networkEdge (meshEndpoint hq) f) : s ≤ angle x y := by
  by_contra! near
  obtain ⟨p, hp, z, hz, endp, bound⟩ :=
    exists_near_endpoint_of_meshArc_proximity qbig hq different no_common spos s_small hx hy near
  rcases endp with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · let t := incidentFace hq e a
    have equal : meshEndpoint hq e a = facetNormal hq t :=
      meshEndpoint_eq_facetNormal_incidentFace hq e a
    rw [equal] at bound
    obtain ⟨b, match_f⟩ := exists_endpoint_eq_of_near_meshArc qbig hq o t r_lt
      (altitude t) f hz bound
    exact no_common a b (equal.trans match_f)
  · let t := incidentFace hq f b
    have equal : meshEndpoint hq f b = facetNormal hq t :=
      meshEndpoint_eq_facetNormal_incidentFace hq f b
    rw [angle_comm, equal] at bound
    obtain ⟨a, match_e⟩ := exists_endpoint_eq_of_near_meshArc qbig hq o t r_lt
      (altitude t) e hp bound
    exact no_common a b (match_e.symm.trans equal.symm)

end Unfoldings.FewestNets.Icosahedron
