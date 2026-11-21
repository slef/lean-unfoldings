module

public import Unfoldings.FewestNets.IcosahedronAdjacentFace
public import Unfoldings.FewestNets.MeshStarFacetNormal

/-! Cyclic model stars identify the actual fine facets and their incident dual arcs. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry

/-- An isometric model of the fine triangles around one actual site. -/
structure MeshStarRealization {q n : ℕ} (a : meshSites q) (star : MeshStar (n + 1)) where
  frame : Space ≃ₗᵢ[ℝ] Space
  face : Fin (n + 1) ↪ MeshFace q
  index : Fin (n + 1) → Equiv.Perm (Fin 3)
  center : frame star.direction = (a : Space)
  corner_eq (k : Fin (n + 1)) (l : Fin 3) :
    inscribedCorners (face k) (index k l) =
      frame ((![star.direction, star.neighborDirection k,
        star.neighborDirection (k + 1)] : Fin 3 → Space) l)
  complete (t : MeshFace q) :
    (a : Space) ∈ Set.range (inscribedCorners t) → t ∈ Set.range face

namespace MeshStarRealization

variable {q n : ℕ} {a : meshSites q} {star : MeshStar (n + 1)}
  (R : MeshStarRealization a star)

theorem site_mem_face (k : Fin (n + 1)) :
    (a : Space) ∈ Set.range (inscribedCorners (R.face k)) :=
  ⟨R.index k 0, (R.corner_eq k 0).trans R.center⟩

theorem facetNormal_eq (hq : 0 < q) (k : Fin (n + 1))
    (outward : 0 < inner ℝ star.direction (star.dual k)) :
    facetNormal hq (R.face k) = R.frame (star.dualDirection k) :=
  facetNormal_eq_map_dualDirection hq _ star k R.frame _ (R.index k).surjective
    (R.corner_eq k) (by rwa [real_inner_comm])

end MeshStarRealization

/-- Supplying the two shared corners establishes incidence with the opposite edge. -/
theorem edgeOpposite_incident_of_corner_pair {q : ℕ} (hq : 0 < q)
    {t s : MeshFace q} {i j k : Fin 3} (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k)
    (hi : inscribedCorners t i ∈ Set.range (inscribedCorners s))
    (hj : inscribedCorners t j ∈ Set.range (inscribedCorners s)) :
    EdgeIncident (edgeOpposite hq t k) s := by
  intro z hz
  obtain ⟨l, eq⟩ := edgeOpposite_incident hq t k z hz
  have same : siteOfCorner t l = z := Subtype.ext eq
  have lk : l ≠ k := (site_mem_edgeOpposite_iff hq t l k).mp (same.symm ▸ hz)
  have table : ∀ i j k l : Fin 3, i ≠ j → i ≠ k → j ≠ k → l ≠ k →
      l = i ∨ l = j := by decide +kernel
  rcases table i j k l ij ik jk lk with h | h
  · exact eq ▸ (h.symm ▸ hi)
  · exact eq ▸ (h.symm ▸ hj)

theorem adjacentFace_eq_of_other_incident {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    {t s : MeshFace q} (different : t ≠ s) (k : Fin 3)
    (hs : EdgeIncident (edgeOpposite hq t k) s) : adjacentFace hq t k = s := by
  let e := edgeOpposite hq t k
  let a := oppositeEndpointIndex hq t e
  have own : incidentFace hq e (!a) = t :=
    incidentFace_eq_of_incident qbig hq t e (edgeOpposite_incident hq t k)
  have other : ∃ b : Bool, incidentFace hq e b = s := by
    rcases (edgeIncident_iff_eq_faces qbig hq e s).mp hs with h | h
    · exact ⟨false, h.symm⟩
    · exact ⟨true, h.symm⟩
  obtain ⟨b, hb⟩ := other
  have flags : b = a ∨ b = (!a) := by cases a <;> cases b <;> decide
  rcases flags with toward | own_index
  · exact (congrArg (incidentFace hq e) toward.symm).trans hb
  · exact (different (own.symm.trans (own_index ▸ hb))).elim

namespace MeshStarRealization

variable {q n : ℕ} {a : meshSites q} {star : MeshStar (n + 1)}
  (R : MeshStarRealization a star)

/-- Across the second corner's opposite edge lies the following triangle. -/
theorem adjacentFace_succ (qbig : 100 ≤ q) (hq : 0 < q) (k : Fin (n + 1))
    (different : k ≠ k + 1) :
    adjacentFace hq (R.face k) (R.index k 1) = R.face (k + 1) := by
  have shared : inscribedCorners (R.face k) (R.index k 2) ∈
      Set.range (inscribedCorners (R.face (k + 1))) := by
    refine ⟨R.index (k + 1) 1, ?_⟩
    rw [R.corner_eq, R.corner_eq]
    rfl
  apply adjacentFace_eq_of_other_incident qbig hq (R.face.injective.ne different)
  refine edgeOpposite_incident_of_corner_pair hq
    ((R.index k).injective.ne (by decide : (0 : Fin 3) ≠ 2))
    ((R.index k).injective.ne (by decide : (0 : Fin 3) ≠ 1))
    ((R.index k).injective.ne (by decide : (2 : Fin 3) ≠ 1)) ?_ shared
  rw [R.corner_eq, show (![star.direction, star.neighborDirection k,
      star.neighborDirection (k + 1)] : Fin 3 → Space) 0 = star.direction by rfl, R.center]
  exact R.site_mem_face (k + 1)

/-- Across the third corner's opposite edge lies the preceding triangle. -/
theorem adjacentFace_pred (qbig : 100 ≤ q) (hq : 0 < q) (k : Fin (n + 1))
    (different : k ≠ k - 1) :
    adjacentFace hq (R.face k) (R.index k 2) = R.face (k - 1) := by
  have shared : inscribedCorners (R.face k) (R.index k 1) ∈
      Set.range (inscribedCorners (R.face (k - 1))) := by
    refine ⟨R.index (k - 1) 2, ?_⟩
    rw [R.corner_eq, R.corner_eq]
    change R.frame (star.neighborDirection (k - 1 + 1)) = R.frame (star.neighborDirection k)
    rw [sub_add_cancel]
  apply adjacentFace_eq_of_other_incident qbig hq (R.face.injective.ne different)
  refine edgeOpposite_incident_of_corner_pair hq
    ((R.index k).injective.ne (by decide : (0 : Fin 3) ≠ 1))
    ((R.index k).injective.ne (by decide : (0 : Fin 3) ≠ 2))
    ((R.index k).injective.ne (by decide : (1 : Fin 3) ≠ 2)) ?_ shared
  rw [R.corner_eq, show (![star.direction, star.neighborDirection k,
      star.neighborDirection (k + 1)] : Fin 3 → Space) 0 = star.direction by rfl, R.center]
  exact R.site_mem_face (k - 1)

end MeshStarRealization

end Unfoldings.FewestNets.Icosahedron
