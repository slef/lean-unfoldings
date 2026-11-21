module

public import Unfoldings.FewestNets.IcosahedronCornerCoordinates
public import Unfoldings.Geometry.CornerHalfplanes

/-! A certified altitude at every cell corner guards the incident Voronoi vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry Cap

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- The distance from a dual vertex to the line joining two successive neighbors,
measured in the gnomonic chart about that vertex. -/
def cornerGuardAltitude {q : ℕ} (o : Orientation ℝ Plane (Fin 2))
    (hq : 0 < q) (t : MeshFace q) (j k : Fin 3) : ℝ :=
  |o.areaForm (adjacentSlope hq t j) (adjacentSlope hq t k)| /
    ‖adjacentSlope hq t k - adjacentSlope hq t j‖

/-- An open altitude disk contains only walls incident to the central facet normal. -/
theorem exists_incident_arc_of_near_voronoiWall {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (o : Orientation ℝ Plane (Fin 2)) (t : MeshFace q) {r : ℝ} (r_lt : r < Real.pi / 2)
    (altitude : ∀ j k : Fin 3, j ≠ k → Real.tan r ≤ cornerGuardAltitude o hq t j k)
    {x : Space} (wall : x ∈ voronoiWalls (fun s : meshSites q => (s : Space)))
    (near : angle (facetNormal hq t) x < r) :
    ∃ j : Fin 3, x ∈ closedMinorArc (facetNormal hq t) (facetNormal hq (adjacentFace hq t j)) ∧
      x ≠ facetNormal hq (adjacentFace hq t j) := by
  classical
  let N := facetNormal hq t
  let L := northFrame N
  let z := centeredSlope N x
  have short : angle N x < Real.pi / 2 := near.trans r_lt
  have Nu := facetNormal_unit hq t
  obtain ⟨sphere, b, c, bc, hb, hc⟩ := wall
  have unit : ‖x‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using sphere
  obtain ⟨i, _, max_i⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3))
    (fun i => inner ℝ x (inscribedCorners t i)) Finset.univ_nonempty
  have exists_j : ∃ j : Fin 3, i ≠ j := by
    have check : ∀ i : Fin 3, ∃ j : Fin 3, i ≠ j := by decide +kernel
    exact check i
  obtain ⟨j, ij⟩ := exists_j
  obtain ⟨k, ik, jk, every⟩ := exists_fin_three_rest i j ij
  let p := adjacentSlope hq t j
  let s := adjacentSlope hq t k
  have inside : ‖z‖ < |o.areaForm p s| / ‖s - p‖ := by
    rw [centeredSlope_norm Nu unit short]
    exact (Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two (angle_nonneg _ _) r_lt near).trans_le
      (altitude j k jk)
  have gap_nonneg (l : Fin 3) : 0 ≤ cornerGap hq t i l z := by
    change 0 ≤ cornerGap hq t i l (centeredSlope N x)
    rw [cornerGap_centeredSlope hq t i l unit short]
    exact mul_nonneg (inv_nonneg.mpr (centeredSlope_height_pos Nu unit short).le)
      (sub_nonneg.mpr (max_i l (Finset.mem_univ l)))
  obtain ⟨u, v, up, vp, uv, eq⟩ := exists_corner_coeff_of_halfplanes o
    (cornerGap hq t i k) (cornerGap hq t i j)
    (cornerGap_adjacentSlope_eq_zero qbig hq t ij jk.symm)
    (cornerGap_adjacentSlope_eq_zero qbig hq t ik jk)
    (cornerGap_adjacentSlope_pos qbig hq t ik) (cornerGap_adjacentSlope_pos qbig hq t ij)
    (gap_nonneg k) (gap_nonneg j) inside
  have along_ray (l : Fin 3) (il : i ≠ l) (d : ℝ) (dp : 0 ≤ d) (dsmall : d < 1)
      (slope_eq : z = d • adjacentSlope hq t l) :
      x ∈ closedMinorArc N (facetNormal hq (adjacentFace hq t l)) ∧
        x ≠ facetNormal hq (adjacentFace hq t l) := by
    refine ⟨mem_closedMinorArc_adjacent_of_slope_segment qbig hq t l unit short ?_, ?_⟩
    · exact ⟨1 - d, d, by linarith, dp, by ring, by simpa only [smul_zero, zero_add]
        using slope_eq.symm⟩
    · intro far
      have h := congrArg (cornerGap hq t i l) slope_eq
      rw [map_smul, smul_eq_mul] at h
      have slope_at_far : z = adjacentSlope hq t l :=
        congrArg (centeredSlope N) far
      rw [slope_at_far] at h
      have strict := mul_lt_mul_of_pos_right dsmall (cornerGap_adjacentSlope_pos qbig hq t il)
      rw [one_mul, ← h] at strict
      exact (lt_irrefl _ strict)
  by_cases eu : u = 0
  · exact ⟨k, along_ray k ik v vp (by linarith only [uv, eu])
      (by simpa only [eu, zero_smul, zero_add] using eq)⟩
  by_cases ev : v = 0
  · exact ⟨j, along_ray j ij u up (by linarith only [uv, ev])
      (by simpa only [ev, zero_smul, add_zero] using eq)⟩
  have upos : 0 < u := lt_of_le_of_ne up (Ne.symm eu)
  have vpos : 0 < v := lt_of_le_of_ne vp (Ne.symm ev)
  have αpos : 0 < 1 - (u + v) := sub_pos.mpr uv
  let a := siteOfCorner t i
  have common_corner (w : meshSites q)
      (top : x ∈ finiteHullNormalCone (fun y : meshSites q => (y : Space)) w) : w = a := by
    let d : Space := (a : Space) - (w : Space)
    let P := facetNormal hq (adjacentFace hq t j)
    let Q := facetNormal hq (adjacentFace hq t k)
    let gap (y : Plane) := inner ℝ (northLift y) (L d)
    have at_N : (a : Space) ∈ Set.range (inscribedCorners t) := Set.mem_range_self i
    have at_P : (a : Space) ∈ Set.range (inscribedCorners (adjacentFace hq t j)) :=
      (corner_mem_adjacentFace_iff qbig hq t j i).mpr ij
    have at_Q : (a : Space) ∈ Set.range (inscribedCorners (adjacentFace hq t k)) :=
      (corner_mem_adjacentFace_iff qbig hq t k i).mpr ik
    have gp : gap p = (L P 2)⁻¹ * inner ℝ P d :=
      inner_northLift_centeredSlope Nu (facetNormal_unit hq _)
        (facetNormal_angle_adjacent_lt qbig hq t j) d
    have gq : gap s = (L Q 2)⁻¹ * inner ℝ Q d :=
      inner_northLift_centeredSlope Nu (facetNormal_unit hq _)
        (facetNormal_angle_adjacent_lt qbig hq t k) d
    have gn : gap 0 = inner ℝ N d := by
      change inner ℝ (northLift 0) (L d) = _
      rw [← northFrame_center N Nu, LinearIsometryEquiv.inner_map_map]
    have gz : gap z = (L x 2)⁻¹ * inner ℝ x d :=
      inner_northLift_centeredSlope Nu unit short d
    have slope_sum : gap z = (1 - (u + v)) * gap 0 + u * gap p + v * gap s := by
      unfold gap
      rw [eq, northLift_cornerCombination, inner_add_left, inner_add_left,
        real_inner_smul_left, real_inner_smul_left, real_inner_smul_left]
    have pg : 0 < (L P 2)⁻¹ := inv_pos.mpr
      (centeredSlope_height_pos Nu (facetNormal_unit hq _)
        (facetNormal_angle_adjacent_lt qbig hq t j))
    have qg : 0 < (L Q 2)⁻¹ := inv_pos.mpr
      (centeredSlope_height_pos Nu (facetNormal_unit hq _)
        (facetNormal_angle_adjacent_lt qbig hq t k))
    have nonneg (f : MeshFace q)
        (at_f : (a : Space) ∈ Set.range (inscribedCorners f)) :
        0 ≤ inner ℝ (facetNormal hq f) d := by
      change 0 ≤ inner ℝ (facetNormal hq f) ((a : Space) - (w : Space))
      rw [inner_sub_right]
      exact sub_nonneg.mpr (bound_facetNormal_of_corner qbig hq f a at_f w)
    have nonpos : gap z ≤ 0 := by
      rw [gz]
      apply mul_nonpos_of_nonneg_of_nonpos
        (inv_nonneg.mpr (centeredSlope_height_pos Nu unit short).le)
      change inner ℝ x ((a : Space) - (w : Space)) ≤ 0
      rw [inner_sub_right]
      exact sub_nonpos.mpr (top a)
    have combined := slope_sum ▸ nonpos
    rw [gn, gp, gq, ← mul_assoc, ← mul_assoc] at combined
    have n0 := nonneg t at_N
    have p0 := nonneg (adjacentFace hq t j) at_P
    have q0 := nonneg (adjacentFace hq t k) at_Q
    have pcoef := mul_pos upos pg
    have qcoef := mul_pos vpos qg
    have nterm := mul_nonneg αpos.le n0
    have pterm := mul_nonneg pcoef.le p0
    have qterm := mul_nonneg qcoef.le q0
    have n_eq : inner ℝ N d = 0 := by
      apply le_antisymm _ n0
      by_contra! pos
      have strict := mul_pos αpos pos
      linarith only [strict, pterm, qterm, combined]
    have p_eq : inner ℝ P d = 0 := by
      apply le_antisymm _ p0
      by_contra! pos
      have strict := mul_pos pcoef pos
      linarith only [strict, nterm, qterm, combined]
    have q_eq : inner ℝ Q d = 0 := by
      apply le_antisymm _ q0
      by_contra! pos
      have strict := mul_pos qcoef pos
      linarith only [strict, nterm, pterm, combined]
    have locate (f : MeshFace q) (at_f : (a : Space) ∈ Set.range (inscribedCorners f))
        (eq_f : inner ℝ (facetNormal hq f) d = 0) :
        (w : Space) ∈ Set.range (inscribedCorners f) := by
      change inner ℝ (facetNormal hq f) ((a : Space) - (w : Space)) = 0 at eq_f
      rw [inner_sub_right, sub_eq_zero] at eq_f
      exact (inner_facetNormal_eq_iff_corner qbig hq f a w at_f).mp eq_f.symm
    obtain ⟨l, hl⟩ := locate t at_N n_eq
    rcases every l with same | same | same <;> subst l
    · exact Subtype.ext hl.symm
    · exact False.elim (((corner_mem_adjacentFace_iff qbig hq t j j).mp
        (hl.symm ▸ locate (adjacentFace hq t j) at_P p_eq)) rfl)
    · exact False.elim (((corner_mem_adjacentFace_iff qbig hq t k k).mp
        (hl.symm ▸ locate (adjacentFace hq t k) at_Q q_eq)) rfl)
  exact (bc ((common_corner b hb).trans (common_corner c hc).symm)).elim

end Unfoldings.FewestNets.Icosahedron
