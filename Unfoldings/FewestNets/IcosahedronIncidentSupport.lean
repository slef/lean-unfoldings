module

public import Unfoldings.FewestNets.IcosahedronNormalCellHull
public import Mathlib.Analysis.Convex.Combination

/-! In its open hemisphere, a cell is tested by the adjacent primal sites alone. -/

@[expose] public section

noncomputable section

open scoped Topology BigOperators

namespace Unfoldings.FewestNets.Icosahedron

open Filter InnerProductGeometry

def meshRadialSimplex {q : ℕ} (t : MeshFace q) : Set Space :=
  convexHull ℝ (insert 0 (Set.range (inscribedCorners t)))

theorem mem_meshHull_iff_mem_radialSimplex {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    {x : Space} : x ∈ meshHull q ↔ ∃ t : MeshFace q, x ∈ meshRadialSimplex t := by
  constructor
  · intro hx
    obtain ⟨t, w, nonnegative, expansion⟩ := radialMesh_cover hq x
    have total : (∑ i, w i) ≤ 1 := by
      have bound := meshGauge_le_one_of_mem_hull qbig hq t hx
      rw [expansion, map_sum] at bound
      simpa only [map_smul, smul_eq_mul, meshGauge_corner, mul_one] using bound
    let β : Fin 4 → ℝ := Fin.cons (1 - ∑ i, w i) w
    let p : Fin 4 → Space := Fin.cons (0 : Space) (inscribedCorners t)
    refine ⟨t, mem_convexHull_of_exists_fintype β p ?_ ?_ ?_ ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => nonnegative j) i
      exact sub_nonneg.mpr total
    · rw [Fin.sum_univ_succ]
      change 1 - (∑ i, w i) + (∑ i, w i) = 1
      ring
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_range_self j)
    · rw [Fin.sum_univ_succ]
      change (1 - (∑ i, w i)) • (0 : Space) + (∑ i, w i • inscribedCorners t i) = x
      simpa only [smul_zero, zero_add] using expansion.symm
  · rintro ⟨t, ht⟩
    apply (convexHull_mono (s := insert 0 (Set.range (inscribedCorners t))) ?_) ht
    rintro _ (rfl | ⟨i, rfl⟩)
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨(t, i), rfl⟩

/-- An extreme unit site belongs to a radial simplex only at one of its unit corners. -/
theorem meshSite_mem_radialSimplex_iff {q : ℕ} (hq : 0 < q) (a : meshSites q) (t : MeshFace q) :
    (a : Space) ∈ meshRadialSimplex t ↔ (a : Space) ∈ Set.range (inscribedCorners t) := by
  refine ⟨fun hx => ?_, fun h => subset_convexHull ℝ _ (Set.mem_insert_of_mem _ h)⟩
  by_contra absent
  have unit := meshSites_unit hq a
  have subset : meshRadialSimplex t ⊆ {x | inner ℝ (a : Space) x < 1} := by
    apply convexHull_min
    · rintro _ (rfl | ⟨i, rfl⟩)
      · simp
      · apply (inner_lt_one_iff_real_of_norm_eq_one unit (inscribedCorners_unit hq t i)).mpr
        intro same
        exact absent ⟨i, same.symm⟩
    · exact convex_halfSpace_lt (innerSL ℝ (a : Space)).toLinearMap.isLinear 1
  have bad : inner ℝ (a : Space) (a : Space) < 1 := subset hx
  rw [real_inner_self_eq_norm_sq, unit, one_pow] at bad
  exact (lt_irrefl _ bad)

/-- Checking every neighbor across the complete fine star is enough for the actual
normal cone. The proof uses the closed radial simplices near the site. -/
theorem mem_normalCone_of_incident_triangle_support {q : ℕ}
    (qbig : 100 ≤ q) (hq : 0 < q) (a : meshSites q) (n : Space)
    (upward : 0 < inner ℝ n (a : Space))
    (neighbors : ∀ t : MeshFace q, (a : Space) ∈ Set.range (inscribedCorners t) →
      ∀ k, inner ℝ n (inscribedCorners t k) ≤ inner ℝ n (a : Space)) :
    n ∈ finiteHullNormalCone (fun b : meshSites q => (b : Space)) a := by
  intro b
  by_contra! strict
  let u := (a : Space)
  let v := (b : Space)
  let z (δ : ℝ) := (1 - δ) • u + δ • v
  have near (t : MeshFace q) : ∀ᶠ x in 𝓝 u, x ∈ meshRadialSimplex t →
      (a : Space) ∈ Set.range (inscribedCorners t) := by
    by_cases present : (a : Space) ∈ Set.range (inscribedCorners t)
    · exact Eventually.of_forall (fun _ _ => present)
    · have compact : IsCompact (meshRadialSimplex t) :=
        ((Set.finite_range _).insert 0).isCompact_convexHull ℝ
      have excl : u ∉ meshRadialSimplex t := (meshSite_mem_radialSimplex_iff hq a t).not.mpr present
      filter_upwards [compact.isClosed.isOpen_compl.mem_nhds excl] with x outside
      exact fun h => (outside h).elim
  have tend : Tendsto z (𝓝 0) (𝓝 u) := by
    have continuous : Continuous z := by unfold z; fun_prop
    simpa only [z, sub_zero, one_smul, zero_smul, add_zero] using continuous.tendsto 0
  have at_zero : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ t : MeshFace q, z δ ∈ meshRadialSimplex t →
      (a : Space) ∈ Set.range (inscribedCorners t) :=
    tend.eventually (Filter.eventually_all.mpr near)
  have close : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ t : MeshFace q, z δ ∈ meshRadialSimplex t →
      (a : Space) ∈ Set.range (inscribedCorners t) :=
    at_zero.filter_mono nhdsWithin_le_nhds
  have less : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), δ < 1 :=
    Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)
  have threshold : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < 1 :=
    less.filter_mono nhdsWithin_le_nhds
  obtain ⟨δ, all, small, pos⟩ := (close.and (threshold.and self_mem_nhdsWithin)).exists
  change 0 < δ at pos
  have one : u ∈ meshHull q := subset_convexHull ℝ _ (Set.mem_insert_of_mem _ a.property)
  have two : v ∈ meshHull q := subset_convexHull ℝ _ (Set.mem_insert_of_mem _ b.property)
  have inside : z δ ∈ meshHull q :=
    (convex_convexHull ℝ _) one two (sub_nonneg.mpr small.le) pos.le (by ring)
  obtain ⟨t, chosen⟩ := (mem_meshHull_iff_mem_radialSimplex qbig hq).mp inside
  have supports : meshRadialSimplex t ⊆ {x | inner ℝ n x ≤ inner ℝ n u} := by
    apply convexHull_min
    · rintro _ (rfl | ⟨i, rfl⟩)
      · change inner ℝ n (0 : Space) ≤ inner ℝ n u
        simpa only [inner_zero_right] using upward.le
      · exact neighbors t (all t chosen) i
    · exact convex_halfSpace_le (innerSL ℝ n).toLinearMap.isLinear _
  have contra : inner ℝ n (z δ) ≤ inner ℝ n u := supports chosen
  simp only [z, inner_add_right, real_inner_smul_right] at contra
  have gain : 0 < δ * (inner ℝ n v - inner ℝ n u) := mul_pos pos (sub_pos.mpr strict)
  linarith only [contra, gain]

end Unfoldings.FewestNets.Icosahedron
