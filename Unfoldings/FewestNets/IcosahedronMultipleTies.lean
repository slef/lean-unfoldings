module

public import Unfoldings.FewestNets.IcosahedronFaceIncidence
public import Unfoldings.FewestNets.MeshStarFacetNormal

/-! A tie of at least three sites is an actual dual network vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open scoped BigOperators

/-- All members of a nonempty finite tie fit in a single fine triangle. -/
theorem exists_meshFace_of_tied_site_set {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    {n : Space} (nonzero : n ≠ 0) (S : Finset (meshSites q)) (hne : S.Nonempty)
    (tie : ∀ a ∈ S, n ∈ finiteHullNormalCone (fun p : meshSites q => (p : Space)) a) :
    ∃ t : MeshFace q, ∀ a ∈ S, (a : Space) ∈ Set.range (inscribedCorners t) := by
  have card_pos := Finset.card_pos.mpr hne
  obtain ⟨a, ha⟩ := hne
  let c := (S.card : ℝ)⁻¹
  have pos : 0 < c := inv_pos.mpr (by exact_mod_cast card_pos)
  let x := ∑ z ∈ S, c • (z : Space)
  have total : (∑ _ ∈ S, c) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast card_pos.ne')
  have site_hull (z : meshSites q) : (z : Space) ∈ meshHull q :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem _ z.property)
  have member : x ∈ meshHull q := (convex_convexHull ℝ _).sum_mem
    (fun _ _ => pos.le) total (fun z _ => site_hull z)
  have bound : meshHull q ⊆ {y | inner ℝ n y ≤ inner ℝ n (a : Space)} := by
    rw [meshHull_eq_convexHull_sites qbig hq]
    apply convexHull_min _ (convex_halfSpace_le (innerSL ℝ n).toLinearMap.isLinear _)
    exact fun y hy => tie a ha ⟨y, hy⟩
  have level : inner ℝ n x = inner ℝ n (a : Space) := by
    dsimp only [x]
    simp only [inner_sum, real_inner_smul_right]
    have same (z : meshSites q) (hz : z ∈ S) : inner ℝ n (z : Space) = inner ℝ n (a : Space) :=
      le_antisymm (tie a ha z) (tie z hz a)
    rw [Finset.sum_congr rfl (fun z hz => congrArg _ (same z hz)), ← Finset.sum_mul, total, one_mul]
  have closed : IsClosed (meshHull q) := (Set.finite_range
    (fun label : MeshFace q × Fin 3 => inscribedCorners label.1 label.2)).insert 0
      |>.isClosed_convexHull ℝ
  have frontier := frontier_of_inner_max closed nonzero member fun y hy => level.symm ▸ bound hy
  rw [frontier_meshHull_eq_triangles qbig hq] at frontier
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp frontier
  rw [meshTriangle_eq_support_slice qbig hq] at ht
  have support_eq : (∑ z ∈ S, c * meshGauge hq t (z : Space)) = 1 := by
    have level : meshGauge hq t x = 1 := ht.2
    simpa only [x, map_sum, map_smul, smul_eq_mul] using level
  have zero : ∑ z ∈ S, c * (1 - meshGauge hq t (z : Space)) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, mul_one, total, support_eq, sub_self]
  refine ⟨t, fun z hz => ?_⟩
  have nonnegative (w : meshSites q) (_ : w ∈ S) : 0 ≤ c * (1 - meshGauge hq t (w : Space)) :=
    mul_nonneg pos.le (sub_nonneg.mpr (meshGauge_le_one_of_mem_hull qbig hq t (site_hull w)))
  have hz' := (Finset.sum_eq_zero_iff_of_nonneg nonnegative).mp zero z hz
  exact (meshGauge_corner_eq_iff qbig hq t z).mp
    (sub_eq_zero.mp ((mul_eq_zero.mp hz').resolve_left pos.ne')).symm

/-- Three distinct maximizing sites determine the unique outward facet normal. -/
theorem exists_facetNormal_of_three_tied_sites {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    {n : Space} (unit : ‖n‖ = 1) (S : Finset (meshSites q)) (size : 3 ≤ S.card)
    (tie : ∀ a ∈ S, n ∈ finiteHullNormalCone (fun p : meshSites q => (p : Space)) a) :
    ∃ t : MeshFace q, n = facetNormal hq t ∧
      ∀ a ∈ S, (a : Space) ∈ Set.range (inscribedCorners t) := by
  classical
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have n_ne : n ≠ 0 := norm_ne_zero_iff.mp (unit.trans_ne one_ne_zero)
  obtain ⟨t, corners⟩ := exists_meshFace_of_tied_site_set qbig hq n_ne S hne tie
  let K := Finset.univ.image (siteOfCorner t)
  have sub : S ⊆ K := by
    intro a ha
    obtain ⟨k, hk⟩ := corners a ha
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, Subtype.ext hk⟩
  have card : K.card = 3 := by
    rw [Finset.card_image_of_injective _ (siteOfCorner_injective hq t),
      Finset.card_univ, Fintype.card_fin]
  have equal : S = K := Finset.eq_of_subset_of_card_le sub (card.symm ▸ size)
  obtain ⟨a, ha⟩ := hne
  obtain ⟨u, hu⟩ := exists_meshSite_inner_pos hq unit
  have pos : 0 < inner ℝ n (a : Space) := hu.trans_le (tie a ha u)
  have values (i : Fin 3) : inner ℝ n (inscribedCorners t i) = inner ℝ n (a : Space) := by
    have mem : siteOfCorner t i ∈ S := equal.symm ▸
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    exact le_antisymm (tie a ha (siteOfCorner t i)) (tie (siteOfCorner t i) mem a)
  have eq := facetNormal_eq_normalize_of_constant_inner hq t n pos values
  rw [NormedSpace.normalize_eq_self_of_norm_eq_one unit] at eq
  exact ⟨t, eq.symm, corners⟩

end Unfoldings.FewestNets.Icosahedron
