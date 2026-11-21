module

public import Unfoldings.FewestNets.IcosahedronFaceIncidence
public import Unfoldings.FewestNets.ExpectedNetworkCharge

/-! Each actual Voronoi side is counted in exactly two cell perimeters. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry
open scoped BigOperators

/-- Spherical perimeter in terms of the lengths of the site's actual incident arcs. -/
def meshSitePerimeter {q : ℕ} [Fintype (MeshEdge q)] (hq : 0 < q) (a : meshSites q) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e : MeshEdge q => a ∈ e.val),
    angle (meshEndpoint hq e false) (meshEndpoint hq e true)

theorem networkLength_eq_half_sum_meshSitePerimeter {q : ℕ} [Fintype (MeshEdge q)]
    [Fintype (meshSites q)] (hq : 0 < q) :
    networkLength (meshEndpoint hq) = (∑ a, meshSitePerimeter hq a) / 2 := by
  classical
  let L (e : MeshEdge q) := angle (meshEndpoint hq e false) (meshEndpoint hq e true)
  change (∑ e, L e) = (∑ a, ∑ e ∈ Finset.univ.filter (fun e : MeshEdge q => a ∈ e.val), L e) / 2
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  have count (e : MeshEdge q) : (∑ a : meshSites q, if a ∈ e.val then L e else 0) = 2 * L e := by
    rw [← Finset.sum_filter]
    have univ_filter : Finset.univ.filter (fun a => a ∈ e.val) = e.val := by ext; simp
    rw [univ_filter, Finset.sum_const, e.property.1]
    simp
  rw [Finset.sum_congr rfl (fun e _ => count e), ← Finset.mul_sum]
  ring

/-- Two distinct triangles have at most one primal edge in common. -/
theorem meshEdge_eq_of_two_incident_faces {q : ℕ} (hq : 0 < q) {t s : MeshFace q}
    (different : t ≠ s) {e f : MeshEdge q} (et : EdgeIncident e t) (es : EdgeIncident e s)
    (ft : EdgeIncident f t) (fs : EdgeIncident f s) : e = f := by
  classical
  by_contra other
  let U := e.val ∪ f.val
  have size : 3 ≤ U.card := by
    by_contra! small
    have small_le : U.card ≤ 2 := Nat.le_of_lt_succ small
    have he := Finset.eq_of_subset_of_card_le (Finset.subset_union_left : e.val ⊆ U)
      (small_le.trans_eq e.property.1.symm)
    have hf := Finset.eq_of_subset_of_card_le (Finset.subset_union_right : f.val ⊆ U)
      (small_le.trans_eq f.property.1.symm)
    exact other (Subtype.ext (he.trans hf.symm))
  let W (r : MeshFace q) : Finset (meshSites q) := Finset.univ.image (siteOfCorner r)
  have full (r : MeshFace q) (er : EdgeIncident e r) (fr : EdgeIncident f r) : U = W r := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      have mem : (a : Space) ∈ Set.range (inscribedCorners r) := by
        rcases Finset.mem_union.mp ha with ha | ha
        · exact er a ha
        · exact fr a ha
      obtain ⟨i, hi⟩ := mem
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, Subtype.ext hi⟩
    · dsimp only [W]
      rw [Finset.card_image_of_injective _ (siteOfCorner_injective hq r),
        Finset.card_univ, Fintype.card_fin]
      exact size
  have same := (full t et ft).symm.trans (full s es fs)
  apply different
  apply meshFace_eq_of_corner_range_eq hq
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    have member : siteOfCorner t i ∈ W t := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rw [same] at member
    obtain ⟨j, _, eq⟩ := Finset.mem_image.mp member
    exact ⟨j, congrArg Subtype.val eq⟩
  · rintro ⟨j, rfl⟩
    have member : siteOfCorner s j ∈ W s := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    rw [← same] at member
    obtain ⟨i, _, eq⟩ := Finset.mem_image.mp member
    exact ⟨i, congrArg Subtype.val eq⟩

end Unfoldings.FewestNets.Icosahedron
