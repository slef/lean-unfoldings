module

public import Unfoldings.FewestNets.IcosahedronVoronoiWalls
public import Unfoldings.FewestNets.IcosahedronNormalIdentity
public import Unfoldings.Geometry.MinorArcEndpoints

/-! Each fine primal edge is incident to exactly the two selected faces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

/-- A fine triangle is incident to an edge when it contains both its sites. -/
def EdgeIncident {q : ℕ} (e : MeshEdge q) (t : MeshFace q) : Prop :=
  ∀ a ∈ e.val, (a : Space) ∈ Set.range (inscribedCorners t)

theorem meshEdgeFaces_left_incident {q : ℕ} (hq : 0 < q) (e : MeshEdge q) :
    EdgeIncident e (meshEdgeFaces hq e).1 :=
  (exists_meshEdge_faces hq e).choose_spec.1

theorem meshEdgeFaces_right_incident {q : ℕ} (hq : 0 < q) (e : MeshEdge q) :
    EdgeIncident e (meshEdgeFaces hq e).2 :=
  (exists_meshEdge_faces hq e).choose_spec.2.1

theorem meshEdgeFaces_ne {q : ℕ} (hq : 0 < q) (e : MeshEdge q) :
    (meshEdgeFaces hq e).1 ≠ (meshEdgeFaces hq e).2 := by
  intro eq
  obtain ⟨k, missing⟩ := (exists_meshEdge_faces hq e).choose_spec.2.2
  change inscribedCorners (meshEdgeFaces hq e).2 k ∉
    Set.range (inscribedCorners (meshEdgeFaces hq e).1) at missing
  rw [eq] at missing
  exact missing (Set.mem_range_self k)

/-- The faces selected for the dual arc exhaust the incidences of its primal edge. -/
theorem edgeIncident_iff_eq_faces {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (e : MeshEdge q) (r : MeshFace q) :
    EdgeIncident e r ↔ r = (meshEdgeFaces hq e).1 ∨ r = (meshEdgeFaces hq e).2 := by
  classical
  refine ⟨fun hr => ?_, ?_⟩
  · let t := (meshEdgeFaces hq e).1
    let s := (meshEdgeFaces hq e).2
    by_cases eq : r = t
    · exact .inl eq
    right
    have absent : ∃ d : Fin 3, inscribedCorners r d ∉ Set.range (inscribedCorners t) := by
      by_contra! all
      have sub : Set.range (inscribedCorners r) ⊆ Set.range (inscribedCorners t) := by
        rintro _ ⟨i, rfl⟩
        exact all i
      exact eq (meshFace_eq_of_corner_range_eq hq r t
        (fin_three_range_eq_of_subset (linearIndependent_inscribedCorners hq r).injective sub))
    obtain ⟨a, b, different, pair⟩ := meshEdge_has_vertices e
    have ha : a ∈ e.val := by rw [pair]; simp
    have hb : b ∈ e.val := by rw [pair]; simp
    have left := meshEdgeFaces_left_incident hq e
    have right := meshEdgeFaces_right_incident hq e
    have arc : closedMinorArc (facetNormal hq t) (facetNormal hq s) =
        closedMinorArc (facetNormal hq t) (facetNormal hq r) := by
      ext x
      have known := tie_iff_mem_meshEdge_arc qbig hq e a b different ha hb (x := x)
      change _ ↔ x ∈ closedMinorArc (facetNormal hq t) (facetNormal hq s) at known
      exact known.symm.trans (tie_iff_mem_dualArc qbig hq t r a b different (left a ha)
        (left b hb) (hr a ha) (hr b hb) absent)
    have injective := facetNormal_injective qbig hq
    have eq_normal := closedMinorArc_right_eq_of_same
      (facetNormal_unit hq t) (facetNormal_unit hq s)
      (facetNormal_unit hq r)
      (fun same => meshEdgeFaces_ne hq e (injective same)) (fun same => eq (injective same).symm)
      (facetNormal_add_ne_zero_of_shared_corner hq t s (left a ha) (right a ha))
      (facetNormal_add_ne_zero_of_shared_corner hq t r (left a ha) (hr a ha)) arc
    exact (injective eq_normal).symm
  · rintro (rfl | rfl)
    · exact meshEdgeFaces_left_incident hq e
    · exact meshEdgeFaces_right_incident hq e

/-- The primal incidence above an edge has exactly two elements. -/
def meshEdgeIncidentEquivBool {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q) (e : MeshEdge q) :
    {t : MeshFace q // EdgeIncident e t} ≃ Bool := by
  refine (Equiv.ofBijective
    (fun b : Bool => if b then
      ⟨(meshEdgeFaces hq e).2, meshEdgeFaces_right_incident hq e⟩ else
      ⟨(meshEdgeFaces hq e).1, meshEdgeFaces_left_incident hq e⟩) ?_).symm
  constructor
  · intro a b eq
    cases a <;> cases b <;> simp_all [meshEdgeFaces_ne hq e, (meshEdgeFaces_ne hq e).symm]
  · rintro ⟨t, ht⟩
    rcases (edgeIncident_iff_eq_faces qbig hq e t).mp ht with left | right
    · exact ⟨false, Subtype.ext left.symm⟩
    · exact ⟨true, Subtype.ext right.symm⟩

theorem card_edgeIncident {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q) (e : MeshEdge q) :
    Nat.card {t : MeshFace q // EdgeIncident e t} = 2 := by
  rw [Nat.card_congr (meshEdgeIncidentEquivBool qbig hq e), Nat.card_eq_fintype_card]
  decide

end Unfoldings.FewestNets.Icosahedron
