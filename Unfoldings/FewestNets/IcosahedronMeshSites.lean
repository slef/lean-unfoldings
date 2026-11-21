module

public import Unfoldings.FewestNets.IcosahedronMeshFrontier

/-! The distinct unit mesh sites generate the inscribed convex hull. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Set
open scoped BigOperators

instance meshSitesFinite (q : ℕ) : Finite (meshSites q) :=
  (Set.finite_range _).to_subtype

theorem meshSites_unit {q : ℕ} (hq : 0 < q) (x : meshSites q) : ‖(x : Space)‖ = 1 := by
  obtain ⟨⟨t, k⟩, eq⟩ := x.property
  change inscribedCorners t k = (x : Space) at eq
  rw [← eq]
  exact inscribedCorners_unit hq t k

/-- Every open hemisphere contains at least one fine mesh site. -/
theorem exists_meshSite_inner_pos {q : ℕ} (hq : 0 < q) {x : Space} (unit : ‖x‖ = 1) :
    ∃ i : meshSites q, 0 < inner ℝ x (i : Space) := by
  obtain ⟨t, w, nonnegative, eq⟩ := radialMesh_cover hq x
  by_contra! h
  have positive : inner ℝ x x = 1 := by rw [real_inner_self_eq_norm_sq, unit, one_pow]
  have item (k : Fin 3) : inner ℝ x (inscribedCorners t k) ≤ 0 := h ⟨_, ⟨(t, k), rfl⟩⟩
  have sum : ∑ k, w k * inner ℝ x (inscribedCorners t k) ≤ 0 :=
    Finset.sum_nonpos (fun k _ => mul_nonpos_of_nonneg_of_nonpos (nonnegative k) (item k))
  nth_rw 2 [eq] at positive
  rw [inner_sum] at positive
  simp only [real_inner_smul_right] at positive
  linarith only [sum, positive]

theorem hullGauge_pos_of_ne_zero {q : ℕ} (hq : 0 < q) {x : Space} (nonzero : x ≠ 0) :
    0 < hullGauge hq x := by
  obtain ⟨t, ht⟩ := radialMesh_cover hq x
  rw [hullGauge_eq_meshGauge hq t ht]
  obtain ⟨w, nonnegative, eq⟩ := ht
  rw [eq, map_sum]
  simp only [map_smul, meshGauge_corner, smul_eq_mul, mul_one]
  apply lt_of_le_of_ne (Finset.sum_nonneg fun k _ => nonnegative k)
  intro zero
  have all (k : Fin 3) : w k = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => nonnegative k)).mp zero.symm k (Finset.mem_univ k)
  exact nonzero (by simp [eq, all])

theorem exists_meshHull_siteCombination_on_ray {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    {x : Space} (nonzero : x ≠ 0) : ∃ a : ℝ, 0 < a ∧ a • x ∈ convexHull ℝ (meshSites q) := by
  let a := (hullGauge hq x)⁻¹
  have value := hullGauge_pos_of_ne_zero hq nonzero
  have pos : 0 < a := inv_pos.mpr value
  have level : hullGauge hq (a • x) = 1 := by
    rw [hullGauge_smul hq pos.le]
    exact inv_mul_cancel₀ value.ne'
  have frontier : a • x ∈ frontier (meshHull q) := (frontier_meshHull_eq_level qbig hq).symm ▸ level
  rw [frontier_meshHull_eq_triangles qbig hq] at frontier
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp frontier
  refine ⟨a, pos, convexHull_mono ?_ ht⟩
  rintro _ ⟨k, rfl⟩
  exact ⟨(t, k), rfl⟩

theorem zero_mem_convexHull_meshSites {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q) :
    (0 : Space) ∈ convexHull ℝ (meshSites q) := by
  obtain ⟨t, _⟩ := radialMesh_cover hq 0
  let x := inscribedCorners t 0
  have xne : x ≠ 0 := norm_ne_zero_iff.mp ((inscribedCorners_unit hq t 0).trans_ne one_ne_zero)
  have hx : x ∈ convexHull ℝ (meshSites q) := subset_convexHull ℝ _ ⟨(t, 0), rfl⟩
  obtain ⟨a, pos, ha⟩ := exists_meshHull_siteCombination_on_ray qbig hq (neg_ne_zero.mpr xne)
  have denom : 0 < a + 1 := by positivity
  have sum : a / (a + 1) + 1 / (a + 1) = 1 := by rw [← add_div, div_self denom.ne']
  have average := (convex_convexHull ℝ (meshSites q)) hx ha
    (div_nonneg pos.le denom.le) (div_nonneg zero_le_one denom.le) sum
  have eq : (a / (a + 1)) • x + (1 / (a + 1)) • (a • -x) = 0 := by
    rw [smul_smul, smul_neg, ← sub_eq_add_neg, ← sub_smul]
    rw [show 1 / (a + 1) * a = a / (a + 1) by ring, sub_self, zero_smul]
  rwa [eq] at average

/-- The temporary apex of the radial construction is already in the convex hull of the sites. -/
theorem meshHull_eq_convexHull_sites {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q) :
    meshHull q = convexHull ℝ (meshSites q) := by
  apply Set.Subset.antisymm
  · exact convexHull_min
      (insert_subset (zero_mem_convexHull_meshSites qbig hq) (subset_convexHull ℝ _))
      (convex_convexHull ℝ _)
  · exact convexHull_mono (Set.subset_insert _ _)

end Unfoldings.FewestNets.Icosahedron
