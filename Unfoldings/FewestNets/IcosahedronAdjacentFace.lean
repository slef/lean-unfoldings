module

public import Unfoldings.FewestNets.IcosahedronArcSeparation
public import Unfoldings.FewestNets.IcosahedronFaceIncidence
public import Unfoldings.Geometry.MinorArcArclength

/-! The dual ray across each of a triangle's three primal edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry

/-- Index of the endpoint belonging to the other face across an edge. -/
def oppositeEndpointIndex {q : ℕ} (hq : 0 < q) (t : MeshFace q) (e : MeshEdge q) : Bool :=
  if (meshEdgeFaces hq e).1 = t then true else false

def incidentFace {q : ℕ} (hq : 0 < q) (e : MeshEdge q) (b : Bool) : MeshFace q :=
  if b then (meshEdgeFaces hq e).2 else (meshEdgeFaces hq e).1

theorem meshEndpoint_eq_facetNormal_incidentFace {q : ℕ} (hq : 0 < q)
    (e : MeshEdge q) (b : Bool) :
    meshEndpoint hq e b = facetNormal hq (incidentFace hq e b) := by
  cases b <;> rfl

theorem incidentFace_incident {q : ℕ} (hq : 0 < q) (e : MeshEdge q) (b : Bool) :
    EdgeIncident e (incidentFace hq e b) := by
  cases b
  · exact meshEdgeFaces_left_incident hq e
  · exact meshEdgeFaces_right_incident hq e

theorem incidentFace_eq_of_incident {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t : MeshFace q) (e : MeshEdge q) (ht : EdgeIncident e t) :
    incidentFace hq e (!(oppositeEndpointIndex hq t e)) = t := by
  unfold oppositeEndpointIndex
  split
  · next equal => exact equal
  · next other =>
    exact ((edgeIncident_iff_eq_faces qbig hq e t).mp ht).resolve_left
      (fun h => other h.symm) |>.symm

theorem incidentFace_ne_opposite {q : ℕ} (hq : 0 < q) (e : MeshEdge q) (b : Bool) :
    incidentFace hq e b ≠ incidentFace hq e (!b) := by
  cases b
  · exact meshEdgeFaces_ne hq e
  · exact Ne.symm (meshEdgeFaces_ne hq e)

/-- The face across the edge opposite a specified corner. -/
def adjacentFace {q : ℕ} (hq : 0 < q) (t : MeshFace q) (k : Fin 3) : MeshFace q :=
  incidentFace hq (edgeOpposite hq t k) (oppositeEndpointIndex hq t (edgeOpposite hq t k))

theorem adjacentFace_ne {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q) (t : MeshFace q) (k : Fin 3) :
    adjacentFace hq t k ≠ t := by
  intro equal
  exact incidentFace_ne_opposite hq (edgeOpposite hq t k) _
    (equal.trans (incidentFace_eq_of_incident qbig hq t _
      (edgeOpposite_incident hq t k)).symm)

/-- The neighboring face shares exactly the two corners on the crossed edge. -/
theorem corner_mem_adjacentFace_iff {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t : MeshFace q) (k i : Fin 3) :
    inscribedCorners t i ∈ Set.range (inscribedCorners (adjacentFace hq t k)) ↔ i ≠ k := by
  have present (j : Fin 3) (hj : j ≠ k) :
      inscribedCorners t j ∈ Set.range (inscribedCorners (adjacentFace hq t k)) :=
    incidentFace_incident hq _ _ (siteOfCorner t j)
      ((site_mem_edgeOpposite_iff hq t j k).mpr hj)
  refine ⟨fun h equal => ?_, present i⟩
  subst i
  have sub : Set.range (inscribedCorners t) ⊆
      Set.range (inscribedCorners (adjacentFace hq t k)) := by
    rintro _ ⟨j, rfl⟩
    by_cases eq : j = k
    · rwa [eq]
    · exact present j eq
  have same := fin_three_range_eq_of_subset (linearIndependent_inscribedCorners hq t).injective sub
  exact adjacentFace_ne qbig hq t k (meshFace_eq_of_corner_range_eq hq _ _ same).symm

theorem facetNormal_angle_adjacent_lt {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t : MeshFace q) (k : Fin 3) :
    angle (facetNormal hq t) (facetNormal hq (adjacentFace hq t k)) < Real.pi / 2 := by
  let e := edgeOpposite hq t k
  let b := oppositeEndpointIndex hq t e
  have ht := incidentFace_eq_of_incident qbig hq t e (edgeOpposite_incident hq t k)
  change incidentFace hq e (!b) = t at ht
  change angle (facetNormal hq t) (facetNormal hq (incidentFace hq e b)) < _
  rw [← meshEndpoint_eq_facetNormal_incidentFace, ← ht,
    ← meshEndpoint_eq_facetNormal_incidentFace]
  have bound := meshEndpoint_angle_lt_pi_div_two qbig hq e
  cases b
  · exact (angle_comm (meshEndpoint hq e true) (meshEndpoint hq e false)).trans_lt bound
  · exact bound

theorem closedMinorArc_facetNormal_adjacent {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t : MeshFace q) (k : Fin 3) :
    closedMinorArc (facetNormal hq t) (facetNormal hq (adjacentFace hq t k)) =
      closedMinorArc (meshEndpoint hq (edgeOpposite hq t k) false)
        (meshEndpoint hq (edgeOpposite hq t k) true) := by
  let e := edgeOpposite hq t k
  let b := oppositeEndpointIndex hq t e
  have ht := incidentFace_eq_of_incident qbig hq t e (edgeOpposite_incident hq t k)
  change incidentFace hq e (!b) = t at ht
  change closedMinorArc (facetNormal hq t) (facetNormal hq (incidentFace hq e b)) =
    closedMinorArc (meshEndpoint hq e false) (meshEndpoint hq e true)
  rw [← meshEndpoint_eq_facetNormal_incidentFace, ← ht,
    ← meshEndpoint_eq_facetNormal_incidentFace]
  cases b
  · exact closedMinorArc_comm (meshEndpoint hq e true) (meshEndpoint hq e false)
  · rfl

/-- Equality with a supported site characterizes a corner of the facet. -/
theorem inner_facetNormal_eq_iff_corner {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t : MeshFace q) (a z : meshSites q) (at_a : (a : Space) ∈ Set.range (inscribedCorners t)) :
    inner ℝ (facetNormal hq t) (z : Space) = inner ℝ (facetNormal hq t) (a : Space) ↔
      (z : Space) ∈ Set.range (inscribedCorners t) := by
  rw [inner_facetNormal, inner_facetNormal, (meshGauge_corner_eq_iff qbig hq t a).mpr at_a,
    div_left_inj' (norm_pos_iff.mpr (rawFacetNormal_ne_zero hq t)).ne']
  exact meshGauge_corner_eq_iff qbig hq t z

end Unfoldings.FewestNets.Icosahedron
