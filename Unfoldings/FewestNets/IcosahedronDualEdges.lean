module

public import Unfoldings.FewestNets.IcosahedronEdgeIncidence

/-! Either ordering of the incident faces gives the actual dual edge endpoints. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry

/-- The chosen incident pair is any supplied distinct incident pair up to order. -/
theorem meshEdgeFaces_of_incident_pair {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (e : MeshEdge q) (t s : MeshFace q) (different : t ≠ s)
    (ht : EdgeIncident e t) (hs : EdgeIncident e s) :
    meshEdgeFaces hq e = (t, s) ∨ meshEdgeFaces hq e = (s, t) := by
  rcases (edgeIncident_iff_eq_faces qbig hq e t).mp ht with first | first
  · rcases (edgeIncident_iff_eq_faces qbig hq e s).mp hs with second | second
    · exact (different (first.trans second.symm)).elim
    · left
      exact Prod.ext first.symm second.symm
  · rcases (edgeIncident_iff_eq_faces qbig hq e s).mp hs with second | second
    · right
      exact Prod.ext second.symm first.symm
    · exact (different (first.trans second.symm)).elim

theorem meshEndpoint_ne {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q) (e : MeshEdge q) :
    meshEndpoint hq e false ≠ meshEndpoint hq e true := by
  intro eq
  exact meshEdgeFaces_ne hq e (facetNormal_injective qbig hq eq)

/-- Every actual dual arc has positive spherical length. -/
theorem meshEndpoint_angle_pos {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q) (e : MeshEdge q) :
    0 < angle (meshEndpoint hq e false) (meshEndpoint hq e true) := by
  apply lt_of_le_of_ne (angle_nonneg _ _)
  intro eq
  have inner := inner_eq_mul_norm_of_angle_eq_zero eq.symm
  rw [meshEndpoint_unit, meshEndpoint_unit, one_mul] at inner
  have lt := (inner_lt_one_iff_real_of_norm_eq_one (meshEndpoint_unit hq e false)
    (meshEndpoint_unit hq e true)).mpr (meshEndpoint_ne qbig hq e)
  exact lt.ne inner

end Unfoldings.FewestNets.Icosahedron
