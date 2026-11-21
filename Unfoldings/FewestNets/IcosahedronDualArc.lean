module

public import Unfoldings.FewestNets.IcosahedronSharedEdges
public import Unfoldings.FewestNets.IcosahedronVoronoiTies
public import Unfoldings.Geometry.MinorArcCone
public import Unfoldings.Geometry.SupportingHingeNormalCone

/-! The normals tied across one fine edge are exactly its dual minor arc. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open NormedSpace

private theorem range_eq_of_subset {v w : Fin 3 → Space}
    (inj : Function.Injective v) (sub : Set.range v ⊆ Set.range w) :
    Set.range v = Set.range w := by
  choose label same using (fun k => sub (Set.mem_range_self k))
  have injective : Function.Injective label := by
    intro i j eq
    exact inj ((same i).symm.trans ((congrArg w eq).trans (same j)))
  apply sub.antisymm
  rintro _ ⟨j, rfl⟩
  obtain ⟨k, hk⟩ := (Finite.injective_iff_bijective.mp injective).2 j
  exact ⟨k, (hk ▸ same k).symm⟩

private theorem meshSite_of_corner {q : ℕ} (t : MeshFace q) (k : Fin 3) :
    inscribedCorners t k ∈ meshSites q := ⟨(t, k), rfl⟩

private theorem bound_facetNormal_of_corner {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t : MeshFace q) (a : meshSites q) (corner : (a : Space) ∈ Set.range (inscribedCorners t))
    (z : meshSites q) : inner ℝ (facetNormal hq t) (z : Space) ≤
      inner ℝ (facetNormal hq t) (a : Space) := by
  rw [inner_facetNormal, inner_facetNormal, (meshGauge_corner_eq_iff qbig hq t a).mpr corner]
  exact div_le_div_of_nonneg_right (meshGauge_le_one_of_mem_hull qbig hq t
    (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ z.property))) (norm_nonneg _)

/-- A shared edge between distinct fine triangles has precisely the closed
arc between their two outward unit normals as its spherical normal cone. -/
theorem tie_iff_mem_dualArc {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q) (t s : MeshFace q)
    (a b : meshSites q) (different : a ≠ b)
    (at_left_a : (a : Space) ∈ Set.range (inscribedCorners t))
    (at_left_b : (b : Space) ∈ Set.range (inscribedCorners t))
    (at_right_a : (a : Space) ∈ Set.range (inscribedCorners s))
    (at_right_b : (b : Space) ∈ Set.range (inscribedCorners s))
    (opposite : ∃ d : Fin 3, inscribedCorners s d ∉ Set.range (inscribedCorners t))
    {x : Space} :
    (‖x‖ = 1 ∧ x ∈ finiteHullNormalCone (fun p : meshSites q => (p : Space)) a ∧
      x ∈ finiteHullNormalCone (fun p : meshSites q => (p : Space)) b) ↔
      x ∈ closedMinorArc (facetNormal hq t) (facetNormal hq s) := by
  have positive (f : MeshFace q) (ha : (a : Space) ∈ Set.range (inscribedCorners f)) :
      0 < inner ℝ (facetNormal hq f) (a : Space) := by
    obtain ⟨k, eq⟩ := ha
    rw [← eq]
    exact inner_facetNormal_corner_pos hq f k
  have nonantipodal : facetNormal hq t + facetNormal hq s ≠ 0 := by
    intro eq
    have sum := congrArg (fun v => inner ℝ v (a : Space)) eq
    rw [inner_add_left, inner_zero_left] at sum
    linarith only [sum, positive t at_left_a, positive s at_right_a]
  rw [mem_closedMinorArc_iff_nonnegative_combination
    (facetNormal_unit hq t) (facetNormal_unit hq s) nonantipodal]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨ha, hb⟩
    obtain ⟨i, hi⟩ := at_left_a
    obtain ⟨j, hj⟩ := at_left_b
    have ij : i ≠ j := by
      intro eq
      exact different (Subtype.ext (hi.symm.trans ((congrArg (inscribedCorners t) eq).trans hj)))
    obtain ⟨k, ik, jk, every⟩ := exists_fin_three_rest i j ij
    obtain ⟨d, hd⟩ := opposite
    have hc : inscribedCorners t k ∉ Set.range (inscribedCorners s) := by
      intro present
      have sub : Set.range (inscribedCorners t) ⊆ Set.range (inscribedCorners s) := by
        rintro _ ⟨l, rfl⟩
        rcases every l with rfl | rfl | rfl
        · rw [hi]
          exact at_right_a
        · rw [hj]
          exact at_right_b
        · exact present
      exact hd ((range_eq_of_subset (linearIndependent_inscribedCorners hq t).injective sub).ge
        (Set.mem_range_self d))
    have independent := (permuted_triangle_corners (linearIndependent_inscribedCorners hq t)
      ij ik jk).1
    rw [hi, hj] at independent
    let cSite : meshSites q := ⟨_, meshSite_of_corner t k⟩
    let dSite : meshSites q := ⟨_, meshSite_of_corner s d⟩
    have strict_t : meshGauge hq t (dSite : Space) < 1 :=
      lt_of_le_of_ne (meshGauge_le_one_of_mem_hull qbig hq t
        (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ dSite.property)))
        (fun eq => hd ((meshGauge_corner_eq_iff qbig hq t dSite).mp eq))
    have strict_s : meshGauge hq s (cSite : Space) < 1 :=
      lt_of_le_of_ne (meshGauge_le_one_of_mem_hull qbig hq s
        (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ cSite.property)))
        (fun eq => hc ((meshGauge_corner_eq_iff qbig hq s cSite).mp eq))
    obtain ⟨u, v, up, vp, eq⟩ := exists_nonnegative_combination_of_hinge_tie
      (n := rawFacetNormal hq t) (m := rawFacetNormal hq s) independent
      (by rw [inner_rawFacetNormal, ← hi, meshGauge_corner])
      (by rw [inner_rawFacetNormal, ← hj, meshGauge_corner])
      (by rw [inner_rawFacetNormal, meshGauge_corner])
      (by simpa only [inner_rawFacetNormal] using strict_t)
      (by rw [inner_rawFacetNormal]; exact (meshGauge_corner_eq_iff qbig hq s a).mpr at_right_a)
      (by rw [inner_rawFacetNormal]; exact (meshGauge_corner_eq_iff qbig hq s b).mpr at_right_b)
      (by rw [inner_rawFacetNormal, meshGauge_corner])
      (by simpa only [inner_rawFacetNormal] using strict_s)
      (le_antisymm (ha b) (hb a)) (ha cSite) (ha dSite)
    refine ⟨u * ‖rawFacetNormal hq t‖, v * ‖rawFacetNormal hq s‖,
      mul_nonneg up (norm_nonneg _), mul_nonneg vp (norm_nonneg _), ?_⟩
    rw [eq]
    simp only [mul_smul, facetNormal, norm_smul_normalize]
  · rintro ⟨u, v, up, vp, rfl⟩
    constructor
    · intro z
      simp only [inner_add_left, real_inner_smul_left]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (bound_facetNormal_of_corner qbig hq t a at_left_a z) up)
        (mul_le_mul_of_nonneg_left (bound_facetNormal_of_corner qbig hq s a at_right_a z) vp)
    · intro z
      simp only [inner_add_left, real_inner_smul_left]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (bound_facetNormal_of_corner qbig hq t b at_left_b z) up)
        (mul_le_mul_of_nonneg_left (bound_facetNormal_of_corner qbig hq s b at_right_b z) vp)

end Unfoldings.FewestNets.Icosahedron
