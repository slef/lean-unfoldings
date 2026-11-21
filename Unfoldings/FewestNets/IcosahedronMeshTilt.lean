module

public import Unfoldings.FewestNets.IcosahedronDualEdges
public import Unfoldings.Geometry.EquilateralTriangleCoveringRadius
public import Unfoldings.Geometry.RadialPlaneAngle

/-! The exact uniform angular covering radius used by the finite certification. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Real MeshStar NormedSpace InnerProductGeometry

def meshTilt (q : ℕ) : ℝ := (3 - √5) / q

private theorem coveringConstant_eq :
    (icosahedronEdge / √3) / faceHeight = 3 - √5 := by
  have rootL : 0 < (10 : ℝ) + 2 * √5 := by positivity
  have sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have edgeSq : icosahedronEdge ^ 2 = 2 - 2 * √5 / 5 := by
    rw [icosahedronEdge, div_pow, Real.sq_sqrt rootL.le]
    apply (div_eq_iff rootL.ne').mpr
    linear_combination (4 / 5 : ℝ) * sq
  have hpos : 0 < faceHeight := by
    unfold faceHeight faceHeightSq
    positivity
  have positive : 0 ≤ 3 - √(5 : ℝ) :=
    sub_nonneg.mpr (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
  apply (sq_eq_sq₀ (by unfold icosahedronEdge; positivity) positive).mp
  simp only [div_pow, edgeSq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
    faceHeight_squared, faceHeightSq]
  rw [div_div]
  apply (div_eq_iff (by positivity : (3 : ℝ) * ((5 + 2 * √5) / 15) ≠ 0)).mpr
  linear_combination ((7 - 2 * Real.sqrt 5) / 5) * sq

/-- Every unit direction is within the paper's tilt bound of a unit mesh site. -/
theorem exists_meshSite_angle_le_meshTilt {q : ℕ} (hq : 0 < q)
    {x : Space} (unit : ‖x‖ = 1) : ∃ i : meshSites q, angle x (i : Space) ≤ meshTilt q := by
  have x_ne := norm_ne_zero_iff.mp (unit.trans_ne one_ne_zero)
  obtain ⟨a, a_pos, on_ray⟩ := exists_frontier_on_positive_ray
    ((Set.finite_range rawVertex).isCompact_convexHull ℝ) (convex_convexHull ℝ _)
    zero_mem_interior_hull x_ne
  have front : a • x ∈ frontier hull := by simpa only [hull, zero_add, sub_zero] using on_ray
  obtain ⟨t, present⟩ := exists_chordTriangle_of_frontier hq front
  obtain ⟨e, mapCorners⟩ := exists_modelFace_isometry t.1
  have formula (k : Fin 3) : chordCorners t k = radius • e (modelGridCorners t.2 k) := by
    rw [map_modelGridCorners t e mapCorners, smul_smul, mul_inv_cancel₀ radius_pos.ne', one_smul]
  let n := e modelNormal
  have n_unit : ‖n‖ = 1 := (e.norm_map modelNormal).trans modelNormal_unit
  have h_pos : 0 < faceHeight := by
    unfold faceHeight faceHeightSq
    positivity
  have height (k : Fin 3) : inner ℝ n (chordCorners t k) = radius * faceHeight := by
    rw [formula, real_inner_smul_right]
    change radius * inner ℝ (e modelNormal) (e (modelGridCorners t.2 k)) = _
    rw [e.inner_map_map, inner_modelNormal_modelGridCorners]
  have z_height : inner ℝ n (a • x) = radius * faceHeight := by
    exact convexHull_min (by rintro _ ⟨k, rfl⟩; exact height k)
      (convex_hyperplane (innerSL ℝ n).toLinearMap.isLinear (radius * faceHeight)) present
  let L := radius * (icosahedronEdge / q)
  have L_pos : 0 ≤ L := mul_nonneg radius_pos.le (div_nonneg (by unfold icosahedronEdge; positivity)
    (Nat.cast_nonneg _))
  have edges (i j : Fin 3) (ne : i ≠ j) : ‖chordCorners t i - chordCorners t j‖ = L := by
    rw [formula i, formula j, ← smul_sub, ← map_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos radius_pos, e.norm_map, norm_sub_modelGridCorners t.2 ne]
  obtain ⟨k, near⟩ := exists_corner_norm_le_of_equilateral L_pos edges present
  refine ⟨⟨inscribedCorners t k, ⟨(t, k), rfl⟩⟩, ?_⟩
  have ang := angle_normalize_le_div_planeHeight n_unit (mul_pos radius_pos h_pos)
    z_height (height k)
  rw [normalize_smul_of_pos a_pos, normalize_eq_self_of_norm_eq_one unit] at ang
  change angle x (NormedSpace.normalize (chordCorners t k)) ≤ meshTilt q
  apply ang.trans
  have q_real : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  calc
    _ ≤ (L / √3) / (radius * faceHeight) :=
      div_le_div_of_nonneg_right near (mul_pos radius_pos h_pos).le
    _ = ((icosahedronEdge / √3) / faceHeight) / q := by
      dsimp only [L]
      field_simp [radius_pos.ne', h_pos.ne', q_real]
    _ = meshTilt q := by rw [coveringConstant_eq, meshTilt]

/-- Maximizing sites inherit the same angular bound as the nearest site. -/
theorem angle_le_meshTilt_of_mem_normalCone {q : ℕ} (hq : 0 < q) {n : Space} (unit : ‖n‖ = 1)
    (s : meshSites q) (hn : n ∈ finiteHullNormalCone (fun i : meshSites q => (i : Space)) s) :
    angle n (s : Space) ≤ meshTilt q := by
  obtain ⟨i, small⟩ := exists_meshSite_angle_le_meshTilt hq unit
  apply le_trans _ small
  simp only [angle, unit, meshSites_unit hq s, meshSites_unit hq i, one_mul, div_one]
  exact Real.arccos_le_arccos (hn i)

/-- Both incident face normals are within the site tilt of a shared corner. -/
theorem meshEndpoint_angle_le_two_meshTilt {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (e : MeshEdge q) :
    angle (meshEndpoint hq e false) (meshEndpoint hq e true) ≤ 2 * meshTilt q := by
  obtain ⟨a, b, _, pair⟩ := meshEdge_has_vertices e
  have ha : a ∈ e.val := by
    classical
    rw [pair]
    simp
  let t := (meshEdgeFaces hq e).1
  let s := (meshEdgeFaces hq e).2
  have ltie : facetNormal hq t ∈ finiteHullNormalCone (fun i : meshSites q => (i : Space)) a :=
    fun j => bound_facetNormal_of_corner qbig hq t a (meshEdgeFaces_left_incident hq e a ha) j
  have rtie : facetNormal hq s ∈ finiteHullNormalCone (fun i : meshSites q => (i : Space)) a :=
    fun j => bound_facetNormal_of_corner qbig hq s a (meshEdgeFaces_right_incident hq e a ha) j
  have left := angle_le_meshTilt_of_mem_normalCone hq (facetNormal_unit hq t) a ltie
  have right := angle_le_meshTilt_of_mem_normalCone hq (facetNormal_unit hq s) a rtie
  have tri := angle_le_angle_add_angle (facetNormal hq t) (a : Space) (facetNormal hq s)
  rw [angle_comm (a : Space) (facetNormal hq s)] at tri
  change angle (facetNormal hq t) (facetNormal hq s) ≤ _
  linarith only [tri, left, right]

/-- A uniform short-arc bound on every edge of either endpoint network. -/
theorem meshEndpoint_angle_lt_twice_step {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (e : MeshEdge q) :
    angle (meshEndpoint hq e false) (meshEndpoint hq e true) < 2 * (icosahedronEdge / q) := by
  have lo : (2 : ℝ) ≤ √5 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hi : √(5 : ℝ) < 3 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have short : √((10 : ℝ) + 2 * √5) < 4 := by
    apply (Real.sqrt_lt (by positivity) (by norm_num)).mpr
    linarith only [hi]
  have long : 1 < icosahedronEdge := by
    rw [icosahedronEdge, lt_div_iff₀ (by positivity : 0 < √((10 : ℝ) + 2 * √5)), one_mul]
    exact short
  have constant : 3 - √(5 : ℝ) < icosahedronEdge := by
    linarith only [lo, long]
  have q_real : (0 : ℝ) < q := by exact_mod_cast hq
  exact (meshEndpoint_angle_le_two_meshTilt qbig hq e).trans_lt
    (mul_lt_mul_of_pos_left (div_lt_div_of_pos_right constant q_real) (by norm_num))

theorem meshEndpoint_angle_lt_pi_div_two {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (e : MeshEdge q) : angle (meshEndpoint hq e false) (meshEndpoint hq e true) < π / 2 := by
  have digits : (100 : ℝ) ≤ q := by exact_mod_cast qbig
  have q_real : (0 : ℝ) < q := by exact_mod_cast hq
  have small : meshTilt q < 3 / 100 := by
    rw [meshTilt, div_lt_iff₀ q_real]
    linarith only [digits, Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 5)]
  have h := meshEndpoint_angle_le_two_meshTilt qbig hq e
  linarith only [small, h, Real.pi_gt_three]

end Unfoldings.FewestNets.Icosahedron
