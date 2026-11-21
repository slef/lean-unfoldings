module

public import Unfoldings.FewestNets.IcosahedronMeshSites

/-! Each normalized fine triangle is the full slice of its supporting plane. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Set Filter
open scoped BigOperators Topology

private theorem eventually_meshCones_contain_base {q : ℕ} (hq : 0 < q) (y : Space) :
    ∀ᶠ z in 𝓝 y, ∀ s : MeshFace q,
      z ∈ radialTriangleCone (inscribedCorners s) →
        y ∈ radialTriangleCone (inscribedCorners s) := by
  apply Filter.eventually_all.mpr
  intro s
  by_cases contained : y ∈ radialTriangleCone (inscribedCorners s)
  · exact Filter.Eventually.of_forall (fun _ _ => contained)
  have closed := isClosed_radialTriangleCone (linearIndependent_inscribedCorners hq s)
  filter_upwards [closed.isOpen_compl.mem_nhds contained] with z hz member
  exact (hz member).elim

private theorem inside_cone_of_support_eq {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t : MeshFace q) {p : Space} (hp : p ∈ meshHull q) (at_support : meshGauge hq t p = 1) :
    p ∈ radialTriangleCone (inscribedCorners t) := by
  let independent := linearIndependent_inscribedCorners hq t
  let B := radialTriangleBasis independent
  by_contra outside
  have outside' : ¬∀ k : Fin 3, 0 ≤ B.coord k p := by
    simpa only [mem_radialTriangleCone_iff_basis independent, Module.Basis.equivFun_apply,
      Module.Basis.coord_apply] using outside
  push Not at outside'
  obtain ⟨k, negative⟩ := outside'
  have positions : ∀ k : Fin 3, ∃ i j : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    decide +kernel
  obtain ⟨i, j, ij, ik, jk⟩ := positions k
  let a := inscribedCorners t i
  let b := inscribedCorners t j
  let y := (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b
  have in_t : y ∈ radialTriangleCone (inscribedCorners t) :=
    (convex_radialTriangleCone independent) (corner_mem_radialTriangleCone _ i)
      (corner_mem_radialTriangleCone _ j) (by norm_num) (by norm_num) (by norm_num)
  have y_support : meshGauge hq t y = 1 := by
    dsimp only [y, a, b]
    rw [map_add, map_smul, map_smul, meshGauge_corner, meshGauge_corner]
    norm_num [smul_eq_mul]
  have y_hull : y ∈ meshHull q := by
    rw [meshHull_eq_sublevel qbig hq]
    change hullGauge hq y ≤ 1
    rw [hullGauge_eq_meshGauge hq t in_t, y_support]
  have coordinate (l : Fin 3) : B.coord l y =
      (1 / 2 : ℝ) * (if l = i then 1 else 0) + (1 / 2 : ℝ) * (if l = j then 1 else 0) := by
    dsimp only [y, a, b, B]
    rw [map_add, map_smul, map_smul, radialTriangleBasis_coord_corner,
      radialTriangleBasis_coord_corner, smul_eq_mul, smul_eq_mul]
  have y_off (l : Fin 3) (r : ℝ) : y ≠ r • inscribedCorners t l := by
    intro eq
    by_cases same : l = i
    · subst l
      have h := congrArg (B.coord j) eq
      rw [coordinate, map_smul] at h
      change _ = r • (radialTriangleBasis independent).coord j (inscribedCorners t i) at h
      rw [radialTriangleBasis_coord_corner] at h
      norm_num [ij.symm] at h
    · have h := congrArg (B.coord i) eq
      rw [coordinate, map_smul] at h
      change _ = r • (radialTriangleBasis independent).coord i (inscribedCorners t l) at h
      rw [radialTriangleBasis_coord_corner] at h
      norm_num [ij, Ne.symm same] at h
  let path (r : ℝ) := y + r • (p - y)
  have near : Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 y) := by
    have c : Continuous path := by dsimp [path]; fun_prop
    simpa only [ContinuousWithinAt, path, zero_smul, add_zero] using
      (c.continuousWithinAt (s := Ioi (0 : ℝ)) (x := (0 : ℝ)))
  have close := near.eventually (eventually_meshCones_contain_base hq y)
  have positive_times : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  have small_times : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  have times : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r ∈ Set.Ioo 0 1 :=
    positive_times.and small_times
  obtain ⟨r, hr, rpos, rlt⟩ := (close.and times).exists
  obtain ⟨s, in_s⟩ := radialMesh_cover hq (path r)
  have contact := hr s in_s
  have yk : B.coord k y = 0 := by simp [coordinate, ik.symm, jk.symm]
  have path_outside : path r ∉ radialTriangleCone (inscribedCorners t) := by
    intro on_cone
    have nonnegative := (mem_radialTriangleCone_iff_basis independent).mp on_cone k
    change 0 ≤ B.coord k (path r) at nonnegative
    dsimp only [path] at nonnegative
    rw [map_add, map_smul, map_sub, yk, sub_zero, zero_add, smul_eq_mul] at nonnegative
    exact (mul_neg_of_pos_of_neg rpos negative).not_ge nonnegative
  have strict := meshGauge_lt_on_neighbor_of_outside qbig hq t s y_off in_t contact
    in_s path_outside
  have level : meshGauge hq t (path r) = 1 := by
    dsimp only [path]
    rw [map_add, map_smul, map_sub, y_support, at_support, sub_self, smul_zero, add_zero]
  have member : path r ∈ meshHull q := by
    have eq : path r = (1 - r) • y + r • p := by
      dsimp only [path]
      module
    rw [eq]
    exact (convex_convexHull ℝ _) y_hull hp (sub_nonneg.mpr rlt.le) rpos.le (sub_add_cancel 1 r)
  have bound : hullGauge hq (path r) ≤ 1 := by
    rw [meshHull_eq_sublevel qbig hq] at member
    exact member
  rw [level, ← hullGauge_eq_meshGauge hq s in_s] at strict
  exact strict.not_ge bound

/-- A fine-face supporting plane exposes exactly its closed chord triangle. -/
theorem meshTriangle_eq_support_slice {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q) (t : MeshFace q) :
    convexHull ℝ (Set.range (inscribedCorners t)) =
      meshHull q ∩ {x | meshGauge hq t x = 1} := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x member
    obtain ⟨w, nonnegative, total, eq⟩ :=
      TriangleGrid.exists_weights_of_mem_convexHull_range _ member
    have in_cone : x ∈ radialTriangleCone (inscribedCorners t) := ⟨w, nonnegative, eq.symm⟩
    have level : meshGauge hq t x = 1 := by
      rw [← eq, map_sum]
      simpa only [map_smul, meshGauge_corner, smul_eq_mul, mul_one] using total
    refine ⟨?_, level⟩
    rw [meshHull_eq_sublevel qbig hq]
    change hullGauge hq x ≤ 1
    rw [hullGauge_eq_meshGauge hq t in_cone, level]
  · rintro x ⟨hx, at_support⟩
    have level : meshGauge hq t x = 1 := at_support
    obtain ⟨w, nonnegative, eq⟩ := inside_cone_of_support_eq qbig hq t hx level
    have total : ∑ k, w k = 1 := by
      rw [eq, map_sum] at level
      simpa only [map_smul, meshGauge_corner, smul_eq_mul, mul_one] using level
    exact mem_convexHull_of_exists_fintype w _ nonnegative total
      (fun k => Set.mem_range_self k) eq.symm

/-- A unit point in an inscribed triangle is one of its three corners. -/
theorem mem_inscribedCorners_of_unit_mem_triangle {q : ℕ} (hq : 0 < q) (t : MeshFace q)
    {p : Space} (unit : ‖p‖ = 1) (member : p ∈ convexHull ℝ (Set.range (inscribedCorners t))) :
    p ∈ Set.range (inscribedCorners t) := by
  by_contra absent
  obtain ⟨w, nonnegative, total, eq⟩ :=
    TriangleGrid.exists_weights_of_mem_convexHull_range _ member
  have some : ∃ k, 0 < w k := by
    by_contra! none
    have zero (k : Fin 3) : w k = 0 := le_antisymm (none k) (nonnegative k)
    simp [zero] at total
  obtain ⟨k, positive⟩ := some
  have term (j : Fin 3) : inner ℝ p (inscribedCorners t j) < 1 :=
    (inner_lt_one_iff_real_of_norm_eq_one unit (inscribedCorners_unit hq t j)).mpr
      (fun same => absent ⟨j, same.symm⟩)
  have strict : (∑ j, w j * inner ℝ p (inscribedCorners t j)) < ∑ j, w j * 1 :=
    Finset.sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (term j).le (nonnegative j))
      ⟨k, Finset.mem_univ _, mul_lt_mul_of_pos_left (term k) positive⟩
  have normed : inner ℝ p p = 1 := by rw [real_inner_self_eq_norm_sq, unit, one_pow]
  have sum := congrArg (inner ℝ p) eq
  simp only [inner_sum, real_inner_smul_right, normed] at sum
  simp only [sum, mul_one, total] at strict
  exact (lt_irrefl _ strict)

/-- Each fine supporting plane is strict at any site outside its triangle. -/
theorem meshGauge_corner_eq_iff {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t : MeshFace q) (p : meshSites q) :
    meshGauge hq t (p : Space) = 1 ↔ (p : Space) ∈ Set.range (inscribedCorners t) := by
  refine ⟨fun eq => ?_, ?_⟩
  · have hull : (p : Space) ∈ meshHull q :=
      subset_convexHull ℝ _ (Set.mem_insert_of_mem _ p.property)
    apply mem_inscribedCorners_of_unit_mem_triangle hq t (meshSites_unit hq p)
    rw [meshTriangle_eq_support_slice qbig hq]
    exact ⟨hull, eq⟩
  · rintro ⟨k, eq⟩
    rw [← eq, meshGauge_corner]

end Unfoldings.FewestNets.Icosahedron
