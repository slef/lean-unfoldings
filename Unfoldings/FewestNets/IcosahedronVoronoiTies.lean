module

public import Unfoldings.FewestNets.IcosahedronFacetNormals
public import Unfoldings.FewestNets.NormalVoronoi

/-! Every Voronoi tie is associated to an edge of the actual fine triangulation. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

/-- A nonzero supporting functional attains its maximum only at frontier points. -/
theorem frontier_of_inner_max {S : Set Space} (closed : IsClosed S)
    {n x : Space} (nonzero : n ≠ 0) (member : x ∈ S)
    (bound : ∀ y ∈ S, inner ℝ n y ≤ inner ℝ n x) : x ∈ frontier S := by
  rw [frontier, closed.closure_eq, Set.mem_sdiff]
  refine ⟨member, fun inside => ?_⟩
  obtain ⟨ε, eps, ball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp inside)
  let t := ε / (2 * ‖n‖)
  have normpos := norm_pos_iff.mpr nonzero
  have tp : 0 < t := div_pos eps (by positivity)
  have inBall : x + t • n ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos tp]
    dsimp only [t]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < 2 * ‖n‖)]
    nlinarith only [mul_pos eps normpos]
  have le := bound _ (ball inBall)
  rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at le
  have strict := mul_pos tp (pow_pos normpos 2)
  linarith only [le, strict]

/-- The endpoints of a genuine Voronoi tie are corners of a common fine face. -/
theorem exists_meshFace_of_normalCone_tie {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    {n : Space} (nonzero : n ≠ 0) (a b : meshSites q)
    (ha : n ∈ finiteHullNormalCone (fun p : meshSites q => (p : Space)) a)
    (hb : n ∈ finiteHullNormalCone (fun p : meshSites q => (p : Space)) b) :
    ∃ t : MeshFace q, (a : Space) ∈ Set.range (inscribedCorners t) ∧
      (b : Space) ∈ Set.range (inscribedCorners t) := by
  let p := (a : Space)
  let r := (b : Space)
  let x := (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • r
  have p_hull : p ∈ meshHull q := subset_convexHull ℝ _ (Set.mem_insert_of_mem _ a.property)
  have r_hull : r ∈ meshHull q := subset_convexHull ℝ _ (Set.mem_insert_of_mem _ b.property)
  have x_hull : x ∈ meshHull q :=
    (convex_convexHull ℝ _) p_hull r_hull (by norm_num) (by norm_num) (by norm_num)
  have eq : inner ℝ n p = inner ℝ n r := le_antisymm (hb a) (ha b)
  have level : inner ℝ n x = inner ℝ n p := by
    dsimp only [x]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, ← eq]
    ring
  have bound : meshHull q ⊆ {y | inner ℝ n y ≤ inner ℝ n p} := by
    rw [meshHull_eq_convexHull_sites qbig hq]
    apply convexHull_min _ (convex_halfSpace_le (innerSL ℝ n).toLinearMap.isLinear _)
    exact fun y hy => ha ⟨y, hy⟩
  have closed : IsClosed (meshHull q) := (Set.finite_range
    (fun label : MeshFace q × Fin 3 => inscribedCorners label.1 label.2)).insert 0
      |>.isClosed_convexHull ℝ
  have on_frontier := frontier_of_inner_max closed nonzero x_hull fun y hy =>
    level.symm ▸ bound hy
  rw [frontier_meshHull_eq_triangles qbig hq] at on_frontier
  obtain ⟨t, member⟩ := Set.mem_iUnion.mp on_frontier
  rw [meshTriangle_eq_support_slice qbig hq] at member
  have height : meshGauge hq t x = 1 := member.2
  have hp := meshGauge_le_one_of_mem_hull qbig hq t p_hull
  have hr := meshGauge_le_one_of_mem_hull qbig hq t r_hull
  dsimp only [x] at height
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at height
  exact ⟨t, (meshGauge_corner_eq_iff qbig hq t a).mp (by linarith only [height, hp, hr]),
    (meshGauge_corner_eq_iff qbig hq t b).mp (by linarith only [height, hp, hr])⟩

end Unfoldings.FewestNets.Icosahedron
