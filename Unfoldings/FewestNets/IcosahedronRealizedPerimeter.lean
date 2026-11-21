module

public import Unfoldings.FewestNets.IcosahedronRealizedStar
public import Unfoldings.FewestNets.IcosahedronPerimeterCounting
public import Unfoldings.FewestNets.IcosahedronNetworkOfCornerBounds
public import Unfoldings.FewestNets.CheckedMeshPerimeter

/-! Every side of an actual cell is counted once in its cyclic model perimeter. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron.MeshStarRealization

open InnerProductGeometry
open scoped BigOperators

variable {q n : ℕ} {a : meshSites q} {M : MeshStar (n + 1)}
  (R : MeshStarRealization a M)

include R in
theorem meshSitePerimeter_eq_sum [Fintype (MeshEdge q)] (qbig : 100 ≤ q) (hq : 0 < q)
    (flags : ∀ k : Fin (n + 1), k ≠ k + 1 ∧ k ≠ k - 1 ∧ k + 2 ≠ k)
    (outward : ∀ k, 0 < inner ℝ M.direction (M.dual k)) :
    meshSitePerimeter hq a = ∑ k, angle (M.dualDirection k) (M.dualDirection (k + 1)) := by
  classical
  let edge (k : Fin (n + 1)) := edgeOpposite hq (R.face k) (R.index k 1)
  have own (k : Fin (n + 1)) : EdgeIncident (edge k) (R.face k) :=
    edgeOpposite_incident hq _ _
  have next (k : Fin (n + 1)) : EdgeIncident (edge k) (R.face (k + 1)) := by
    rw [← R.adjacentFace_succ qbig hq k (flags k).1]
    exact incidentFace_incident hq _ _
  have compatible (k : Fin (n + 1)) := meshEdgeFaces_of_incident_pair qbig hq
    (edge k) (R.face k) (R.face (k + 1)) (R.face.injective.ne (flags k).1) (own k) (next k)
  have only_two (k : Fin (n + 1)) {t : MeshFace q} (mem : EdgeIncident (edge k) t) :
      t = R.face k ∨ t = R.face (k + 1) := by
    have choice := (edgeIncident_iff_eq_faces qbig hq (edge k) t).mp mem
    rcases compatible k with order | order
    · simpa only [order, Prod.fst, Prod.snd] using choice
    · exact ((by simpa only [order, Prod.fst, Prod.snd] using choice :
        t = R.face (k + 1) ∨ t = R.face k)).symm
  have ones : (1 : Fin (n + 1)) + 1 = 2 := by
    apply Fin.ext
    change (1 % (n + 1) + 1 % (n + 1)) % (n + 1) = 2 % (n + 1)
    rw [← Nat.add_mod]
  have injective : Function.Injective edge := by
    intro k l same
    rcases only_two k (same.symm ▸ own l) with first | second
    · exact (R.face.injective first).symm
    · have l_eq : l = k + 1 := R.face.injective second
      rcases only_two k (same.symm ▸ next l) with prev | prev
      · have h := R.face.injective prev
        rw [l_eq, add_assoc, ones] at h
        exact ((flags k).2.2 h).elim
      · have h := R.face.injective prev
        rw [l_eq] at h
        exact ((flags (k + 1)).1 h.symm).elim
  have center (k : Fin (n + 1)) : siteOfCorner (R.face k) (R.index k 0) = a :=
    Subtype.ext ((R.corner_eq k 0).trans R.center)
  have contains (k : Fin (n + 1)) : a ∈ (edge k).val := by
    rw [← center k]
    exact (site_mem_edgeOpposite_iff hq _ _ _).mpr ((R.index k).injective.ne (by decide))
  have hits (e : MeshEdge q) (he : a ∈ e.val) : ∃ k, edge k = e := by
    let t := (meshEdgeFaces hq e).1
    have ht : EdgeIncident e t := meshEdgeFaces_left_incident hq e
    obtain ⟨k, label⟩ := R.complete t (ht a he)
    have inc : EdgeIncident e (R.face k) := label.symm ▸ ht
    obtain ⟨r, er⟩ := exists_edgeOpposite_eq_of_incident hq (R.face k) e inc
    obtain ⟨j, rfl⟩ := (R.index k).surjective r
    have in_e : a ∈ (edgeOpposite hq (R.face k) (R.index k j)).val := er.symm ▸ he
    have in_center : siteOfCorner (R.face k) (R.index k 0) ∈
        (edgeOpposite hq (R.face k) (R.index k j)).val :=
      Eq.mpr (congrArg (fun b : meshSites q =>
        b ∈ (edgeOpposite hq (R.face k) (R.index k j)).val) (center k)) in_e
    have j0 : j ≠ 0 := fun eq => (site_mem_edgeOpposite_iff hq _ _ _).mp in_center
      (congrArg (R.index k) eq.symm)
    have table : ∀ j : Fin 3, j ≠ 0 → j = 1 ∨ j = 2 := by decide +kernel
    rcases table j j0 with rfl | rfl
    · exact ⟨k, er⟩
    · refine ⟨k - 1, meshEdge_eq_of_two_incident_faces hq
        (R.face.injective.ne (flags k).2.1)
        (by simpa only [sub_add_cancel] using next (k - 1)) (own (k - 1)) inc ?_⟩
      rw [← R.adjacentFace_pred qbig hq k (flags k).2.1, ← er]
      exact incidentFace_incident hq _ _
  have indices : Finset.univ.image edge =
      Finset.univ.filter (fun e : MeshEdge q => a ∈ e.val) := by
    ext e
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨fun ⟨k, eq⟩ => eq ▸ contains k, hits e⟩
  have length (k : Fin (n + 1)) :
      angle (meshEndpoint hq (edge k) false) (meshEndpoint hq (edge k) true) =
        angle (M.dualDirection k) (M.dualDirection (k + 1)) := by
    rcases compatible k with order | order
    · simp only [meshEndpoint, order, Bool.false_eq_true, ite_false, ite_true]
      rw [R.facetNormal_eq hq k (outward k), R.facetNormal_eq hq _ (outward (k + 1))]
      exact R.frame.toLinearIsometry.angle_map _ _
    · simp only [meshEndpoint, order, Bool.false_eq_true, ite_false, ite_true]
      rw [R.facetNormal_eq hq k (outward k), R.facetNormal_eq hq _ (outward (k + 1))]
      exact (R.frame.toLinearIsometry.angle_map _ _).trans (angle_comm _ _)
  unfold meshSitePerimeter
  rw [← indices, Finset.sum_image (fun _ _ _ _ eq => injective eq)]
  exact Finset.sum_congr rfl fun k _ => length k

include R in
theorem meshSitePerimeter_le_arcUpper [Fintype (MeshEdge q)] (qbig : 100 ≤ q) (hq : 0 < q)
    (flags : ∀ k : Fin (n + 1), k ≠ k + 1 ∧ k ≠ k - 1 ∧ k + 2 ≠ k)
    (outward : ∀ k, 0 < inner ℝ M.direction (M.dual k)) :
    meshSitePerimeter hq a ≤ M.arcUpperPerimeter := by
  rw [R.meshSitePerimeter_eq_sum qbig hq flags outward]
  exact M.perimeter_le_arcUpperPerimeter outward

end Unfoldings.FewestNets.Icosahedron.MeshStarRealization
