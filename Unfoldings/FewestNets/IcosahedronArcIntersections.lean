module

public import Unfoldings.FewestNets.IcosahedronMultipleTies

/-! Distinct dual edges can meet only at endpoints of both edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

theorem meshEdge_sites_tied_of_mem_arc {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (e : MeshEdge q) {x : Space} (hx : x ∈ closedMinorArc (meshEndpoint hq e false)
      (meshEndpoint hq e true)) :
    ‖x‖ = 1 ∧ ∀ a ∈ e.val, x ∈ finiteHullNormalCone (fun p : meshSites q => (p : Space)) a := by
  classical
  obtain ⟨a, b, different, pair⟩ := meshEdge_has_vertices e
  have ha : a ∈ e.val := by rw [pair]; simp
  have hb : b ∈ e.val := by rw [pair]; simp
  obtain ⟨unit, first, second⟩ := (tie_iff_mem_meshEdge_arc qbig hq e a b different ha hb).mpr hx
  refine ⟨unit, fun w hw => ?_⟩
  rw [pair, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl
  · exact first
  · exact second

/-- If two different dual arcs intersect, their intersection consists of genuine endpoints. -/
theorem meshEdge_mem_inter_eq_endpoints {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    {e f : MeshEdge q} (different : e ≠ f) {x : Space}
    (he : x ∈ closedMinorArc (meshEndpoint hq e false) (meshEndpoint hq e true))
    (hf : x ∈ closedMinorArc (meshEndpoint hq f false) (meshEndpoint hq f true)) :
    ∃ i j : Bool, x = meshEndpoint hq e i ∧ x = meshEndpoint hq f j := by
  classical
  obtain ⟨unit, etie⟩ := meshEdge_sites_tied_of_mem_arc qbig hq e he
  obtain ⟨_, ftie⟩ := meshEdge_sites_tied_of_mem_arc qbig hq f hf
  let S := e.val ∪ f.val
  have size : 3 ≤ S.card := by
    by_contra! low
    have e_eq : e.val = S := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by
      have ec := e.property.1
      omega)
    have f_eq : f.val = S := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by
      have fc := f.property.1
      omega)
    exact different (Subtype.ext (e_eq.trans f_eq.symm))
  have support (a : meshSites q) (ha : a ∈ S) :
      x ∈ finiteHullNormalCone (fun p : meshSites q => (p : Space)) a := by
    rcases Finset.mem_union.mp ha with ha | ha
    · exact etie a ha
    · exact ftie a ha
  obtain ⟨t, normal, all_corners⟩ :=
    exists_facetNormal_of_three_tied_sites qbig hq unit S size support
  have is_endpoint (g : MeshEdge q) (sub : g.val ⊆ S) :
      ∃ i : Bool, x = meshEndpoint hq g i := by
    have incident : EdgeIncident g t := fun a ha => all_corners a (sub ha)
    rcases (edgeIncident_iff_eq_faces qbig hq g t).mp incident with first | last
    · exact ⟨false, normal.trans (congrArg (facetNormal hq) first)⟩
    · exact ⟨true, normal.trans (congrArg (facetNormal hq) last)⟩
  obtain ⟨i, ei⟩ := is_endpoint e Finset.subset_union_left
  obtain ⟨j, fj⟩ := is_endpoint f Finset.subset_union_right
  exact ⟨i, j, ei, fj⟩

theorem disjoint_meshEdge_arcs_of_nonincident {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    {e f : MeshEdge q} (different : e ≠ f)
    (no_common_endpoint : ∀ a b, meshEndpoint hq e a ≠ meshEndpoint hq f b) :
    Disjoint (closedMinorArc (meshEndpoint hq e false) (meshEndpoint hq e true))
      (closedMinorArc (meshEndpoint hq f false) (meshEndpoint hq f true)) := by
  refine Set.disjoint_left.mpr (fun x he hf => ?_)
  obtain ⟨a, b, left, right⟩ := meshEdge_mem_inter_eq_endpoints qbig hq different he hf
  exact no_common_endpoint a b (left.symm.trans right)

end Unfoldings.FewestNets.Icosahedron
