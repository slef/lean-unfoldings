module

public import Unfoldings.FewestNets.IcosahedronDualArc

/-! The complete Voronoi wall network of the actual inscribed fine mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

/-- An unordered pair of unit sites forming an edge of a fine triangle. -/
def MeshEdge (q : ℕ) :=
  {p : Finset (meshSites q) // p.card = 2 ∧
    ∃ t : MeshFace q, ∀ a ∈ p, (a : Space) ∈ Set.range (inscribedCorners t)}

instance meshEdgeFinite (q : ℕ) : Finite (MeshEdge q) := by
  unfold MeshEdge
  infer_instance

theorem exists_meshEdge_faces {q : ℕ} (hq : 0 < q) (e : MeshEdge q) :
    ∃ faces : MeshFace q × MeshFace q,
      (∀ a ∈ e.val, (a : Space) ∈ Set.range (inscribedCorners faces.1)) ∧
      (∀ a ∈ e.val, (a : Space) ∈ Set.range (inscribedCorners faces.2)) ∧
      ∃ d : Fin 3, inscribedCorners faces.2 d ∉ Set.range (inscribedCorners faces.1) := by
  classical
  obtain ⟨a, b, different, pair⟩ := Finset.card_eq_two.mp e.property.1
  have ha : a ∈ e.val := by rw [pair]; simp
  have hb : b ∈ e.val := by rw [pair]; simp
  obtain ⟨t, ht⟩ := e.property.2
  obtain ⟨i, hi⟩ := ht a ha
  obtain ⟨j, hj⟩ := ht b hb
  have ij : i ≠ j := by
    intro eq
    exact different (Subtype.ext (hi.symm.trans ((congrArg (inscribedCorners t) eq).trans hj)))
  obtain ⟨s, si, sj, rest⟩ := exists_meshNeighbor_of_edge hq t i j ij
  refine ⟨(t, s), ht, ?_, rest⟩
  intro v hv
  rw [pair, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact hi ▸ si
  · exact hj ▸ sj

def meshEdgeFaces {q : ℕ} (hq : 0 < q) (e : MeshEdge q) : MeshFace q × MeshFace q :=
  (exists_meshEdge_faces hq e).choose

def meshEndpoint {q : ℕ} (hq : 0 < q) (e : MeshEdge q) (side : Bool) : Space :=
  facetNormal hq (if side then (meshEdgeFaces hq e).2 else (meshEdgeFaces hq e).1)

theorem meshEndpoint_unit {q : ℕ} (hq : 0 < q) (e : MeshEdge q) (side : Bool) :
    ‖meshEndpoint hq e side‖ = 1 :=
  facetNormal_unit _ _

theorem meshEdge_has_vertices {q : ℕ} (e : MeshEdge q) :
    ∃ a b : meshSites q, a ≠ b ∧ e.val = {a, b} := by
  classical
  exact Finset.card_eq_two.mp e.property.1

theorem tie_iff_mem_meshEdge_arc {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (e : MeshEdge q) (a b : meshSites q) (different : a ≠ b)
    (ha : a ∈ e.val) (hb : b ∈ e.val) {x : Space} :
    (‖x‖ = 1 ∧ x ∈ finiteHullNormalCone (fun p : meshSites q => (p : Space)) a ∧
      x ∈ finiteHullNormalCone (fun p : meshSites q => (p : Space)) b) ↔
      x ∈ closedMinorArc (meshEndpoint hq e false) (meshEndpoint hq e true) := by
  obtain ⟨left, right, opposite⟩ := (exists_meshEdge_faces hq e).choose_spec
  exact tie_iff_mem_dualArc qbig hq _ _ a b different (left a ha) (left b hb)
    (right a ha) (right b hb) opposite

/-- These actual dual minor arcs cover exactly the spherical Voronoi walls. -/
theorem voronoiWalls_eq_meshEdges {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q) :
    voronoiWalls (fun p : meshSites q => (p : Space)) =
      ⋃ e : MeshEdge q, closedMinorArc (meshEndpoint hq e false) (meshEndpoint hq e true) := by
  classical
  ext x
  constructor
  · rintro ⟨onSphere, a, b, different, left, right⟩
    have unit : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using onSphere
    have nonzero : x ≠ 0 := norm_ne_zero_iff.mp (unit.trans_ne one_ne_zero)
    obtain ⟨t, at_a, at_b⟩ := exists_meshFace_of_normalCone_tie qbig hq nonzero a b left right
    let e : MeshEdge q := ⟨{a, b}, Finset.card_eq_two.mpr ⟨a, b, different, rfl⟩, t, by
      intro v hv
      rw [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact at_a
      · exact at_b⟩
    have ha : a ∈ e.val := by simp [e]
    have hb : b ∈ e.val := by simp [e]
    exact Set.mem_iUnion.mpr ⟨e, (tie_iff_mem_meshEdge_arc qbig hq e a b different ha hb).mp
      ⟨unit, left, right⟩⟩
  · intro hx
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
    obtain ⟨a, b, different, pair⟩ := meshEdge_has_vertices e
    have ha : a ∈ e.val := by rw [pair]; simp
    have hb : b ∈ e.val := by rw [pair]; simp
    obtain ⟨unit, left, right⟩ := (tie_iff_mem_meshEdge_arc qbig hq e a b different ha hb).mpr he
    exact ⟨by simpa only [Metric.mem_sphere, dist_zero_right] using unit,
      a, b, different, left, right⟩

end Unfoldings.FewestNets.Icosahedron
