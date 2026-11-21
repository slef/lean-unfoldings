module

public import Unfoldings.Geometry.ComplexTurn
public import Unfoldings.Geometry.ComplexArea
public import Unfoldings.Geometry.PlanarConjugation
public import Unfoldings.Geometry.ChainConstruction
public import Unfoldings.Geometry.PlanarAngleAddition
public import Unfoldings.Geometry.PlanarAngleArea

/-! A consistently oriented fan of angular length at most π lies in a halfplane. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open InnerProductGeometry

private theorem orient_nonneg_of_sum_ray_angles_le_pi {n : ℕ} (ray : Fin (n + 2) → Plane)
    (first : ray 0 ≠ 0)
    (positive : ∀ i : Fin (n + 1), 0 < orient 0 (ray i.castSucc) (ray i.succ))
    (short : (∑ i : Fin (n + 1), angle (ray i.castSucc) (ray i.succ)) ≤ Real.pi) :
    ∀ i, 0 ≤ orient 0 (ray 0) (ray i) := by
  let F : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let a := F (ray 0)
  let z (i : Fin (n + 2)) := starRingEnd ℂ a * F (ray i)
  let turn (i : Fin (n + 1)) := angle (ray i.castSucc) (ray i.succ)
  have ane : a ≠ 0 := by simpa only [a, map_zero] using F.injective.ne first
  have cn : starRingEnd ℂ a ≠ 0 := by
    simpa only [map_zero] using (starRingEnd ℂ).injective.ne ane
  have cross (x y : Plane) : (starRingEnd ℂ (F x) * F y).im = orient 0 x y := by
    have h := orient_complex_repr_zero (F x) (F y)
    change orient 0 (F.symm (F x)) (F.symm (F y)) = _ at h
    simpa only [F.symm_apply_apply] using h.symm
  have positive_z (i : Fin (n + 1)) : 0 < (starRingEnd ℂ (z i.castSucc) * z i.succ).im := by
    have eq : starRingEnd ℂ (z i.castSucc) * z i.succ =
        (Complex.normSq a : ℂ) * (starRingEnd ℂ (F (ray i.castSucc)) * F (ray i.succ)) := by
      simp only [z, map_mul, Complex.conj_conj, Complex.normSq_eq_conj_mul_self]
      ring
    rw [eq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, cross]
    exact mul_pos (Complex.normSq_pos.mpr ane) (positive i)
  have phased (i : Fin (n + 2)) :
      z i = (‖z i‖ : ℂ) * polarRay (Fin.partialSum turn i) := by
    refine Fin.induction ?_ (fun j previous => ?_) i
    · rw [Fin.partialSum_zero, polarRay_zero, mul_one]
      have eq : z 0 = (Complex.normSq a : ℂ) := Complex.normSq_eq_conj_mul_self.symm
      rw [eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)]
    · rw [Fin.partialSum_succ]
      have step := polar_successor_of_positive_cross (Fin.partialSum turn j.castSucc)
        previous (positive_z j)
      have ang : angle (z j.castSucc) (z j.succ) = turn j := by
        simp only [z, turn, Complex.angle_mul_left cn]
        exact F.toLinearIsometry.angle_map _ _
      rwa [ang] at step
  intro i
  have from_zero : 0 ≤ Fin.partialSum turn i := by
    change 0 ≤ ((List.ofFn turn).take i.val).sum
    rw [List.sum_take_ofFn]
    exact Finset.sum_nonneg (fun k _ => angle_nonneg _ _)
  have at_most : Fin.partialSum turn i ≤ Real.pi := by
    apply le_trans _ short
    change ((List.ofFn turn).take i.val).sum ≤ _
    rw [List.sum_take_ofFn]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun k _ _ => angle_nonneg _ _)
  rw [← cross]
  change 0 ≤ (z i).im
  rw [phased i]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, polarRay_im]
  exact mul_nonneg (norm_nonneg _) (Real.sin_nonneg_of_nonneg_of_le_pi from_zero at_most)

/-- The halfplane condition for a short ordered fan follows from its orientation
and actual geometric angles, and is preserved if the fan is reflected. -/
theorem orient_mul_nonneg_of_sum_ray_angles_le_pi {n : ℕ} (ray : Fin (n + 2) → Plane)
    (first : ray 0 ≠ 0)
    (genuine : ∀ i : Fin (n + 1), orient 0 (ray i.castSucc) (ray i.succ) ≠ 0)
    (consistent : ∀ i : Fin (n + 1),
      (0 < orient 0 (ray i.castSucc) (ray i.succ)) ↔
        0 < orient 0 (ray (0 : Fin (n + 1)).castSucc) (ray (0 : Fin (n + 1)).succ))
    (short : (∑ i : Fin (n + 1), angle (ray i.castSucc) (ray i.succ)) ≤ Real.pi) :
    ∀ i, 0 ≤ orient 0 (ray 0) (ray i) *
      orient 0 (ray (0 : Fin (n + 1)).castSucc) (ray (0 : Fin (n + 1)).succ) := by
  intro i
  by_cases h : 0 < orient 0 (ray (0 : Fin (n + 1)).castSucc) (ray (0 : Fin (n + 1)).succ)
  · exact mul_nonneg (orient_nonneg_of_sum_ray_angles_le_pi ray first
      (fun k => (consistent k).mpr h) short i) h.le
  · have neg (k : Fin (n + 1)) : orient 0 (ray k.castSucc) (ray k.succ) < 0 :=
      lt_of_le_of_ne (le_of_not_gt (fun hk => h ((consistent k).mp hk))) (genuine k)
    have reflect_angle (x y : Plane) :
        angle (planeConjugation x) (planeConjugation y) = angle x y :=
      planeConjugation.toLinearIsometry.angle_map x y
    have reflected := orient_nonneg_of_sum_ray_angles_le_pi
      (fun k => planeConjugation (ray k))
      (by simpa only [map_zero] using planeConjugation.injective.ne first)
      (fun k => by rw [orient_planeConjugation]; exact neg_pos.mpr (neg k))
      (by simpa only [reflect_angle] using short) i
    rw [orient_planeConjugation] at reflected
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonneg.mp reflected) (neg 0).le

/-- The angle from the first ray strictly orders every ray of a short fan. -/
theorem strictMono_angle_first_of_short_fan {n : ℕ} (ray : Fin (n + 2) → Plane)
    (genuine : ∀ i, ray i ≠ 0)
    (nonzero : ∀ i : Fin (n + 1), orient 0 (ray i.castSucc) (ray i.succ) ≠ 0)
    (consistent : ∀ i : Fin (n + 1),
      (0 < orient 0 (ray i.castSucc) (ray i.succ)) ↔
        0 < orient 0 (ray (0 : Fin (n + 1)).castSucc) (ray (0 : Fin (n + 1)).succ))
    (short : (∑ i : Fin (n + 1), angle (ray i.castSucc) (ray i.succ)) ≤ Real.pi) :
    StrictMono (fun i => angle (ray 0) (ray i)) := by
  have left_turn (x y z : Plane) (xn : x ≠ 0) (yn : y ≠ 0)
      (xy : 0 ≤ orient 0 x y) (xz : 0 ≤ orient 0 x z) (yz : 0 < orient 0 y z) :
      angle x y < angle x z := by
    have positive : 0 < angle y z := by
      by_contra! not_positive
      have zero := le_antisymm not_positive (angle_nonneg y z)
      have area := abs_orient_eq_sin_angle_mul_norm y z
      rw [zero, Real.sin_zero, zero_mul] at area
      exact (ne_of_gt yz) (abs_eq_zero.mp area)
    linarith only [positive, angle_add_of_orient_nonneg xn yn xy xz yz]
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have half := orient_mul_nonneg_of_sum_ray_angles_le_pi ray (genuine 0)
    nonzero consistent short
  let s := orient 0 (ray (0 : Fin (n + 1)).castSucc) (ray (0 : Fin (n + 1)).succ)
  rcases lt_or_gt_of_ne (nonzero 0) with neg | pos
  · have neg_i : orient 0 (ray i.castSucc) (ray i.succ) < 0 :=
      lt_of_le_of_ne (le_of_not_gt (fun h => (not_lt_of_ge neg.le) ((consistent i).mp h)))
        (nonzero i)
    have half_neg (j) : orient 0 (ray 0) (ray j) ≤ 0 := by
      have h := half j
      change 0 ≤ orient 0 (ray 0) (ray j) * s at h
      exact nonpos_of_mul_nonneg_left h neg
    have reflect_angle (x y : Plane) :
        angle (planeConjugation x) (planeConjugation y) = angle x y :=
      planeConjugation.toLinearIsometry.angle_map x y
    have less := left_turn (planeConjugation (ray 0)) (planeConjugation (ray i.castSucc))
      (planeConjugation (ray i.succ))
      (by simpa only [map_zero] using planeConjugation.injective.ne (genuine 0))
      (by simpa only [map_zero] using planeConjugation.injective.ne (genuine i.castSucc))
      (by rw [orient_planeConjugation]; exact neg_nonneg.mpr (half_neg i.castSucc))
      (by rw [orient_planeConjugation]; exact neg_nonneg.mpr (half_neg i.succ))
      (by rw [orient_planeConjugation]; exact neg_pos.mpr neg_i)
    simpa only [reflect_angle] using less
  · have half_pos (j) : 0 ≤ orient 0 (ray 0) (ray j) := by
      have h := half j
      change 0 ≤ orient 0 (ray 0) (ray j) * s at h
      exact nonneg_of_mul_nonneg_left h pos
    exact left_turn (ray 0) (ray i.castSucc) (ray i.succ) (genuine 0) (genuine i.castSucc)
      (half_pos i.castSucc) (half_pos i.succ) ((consistent i).mpr pos)

private theorem inner_coordinates (x y : Plane) :
    inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

theorem orient_zero_of_orthogonal_pair {u x y : Plane} (un : u ≠ 0)
    (hx : inner ℝ u x = 0) (hy : inner ℝ u y = 0) : orient 0 x y = 0 := by
  rw [inner_coordinates] at hx hy
  have zero0 : u 0 * orient 0 x y = 0 := by
    simp only [orient, PiLp.zero_apply, sub_zero]
    linear_combination y 1 * hx - x 1 * hy
  have zero1 : u 1 * orient 0 x y = 0 := by
    simp only [orient, PiLp.zero_apply, sub_zero]
    linear_combination x 0 * hy - y 0 * hx
  by_contra h
  have c0 := (mul_eq_zero.mp zero0).resolve_right h
  have c1 := (mul_eq_zero.mp zero1).resolve_right h
  apply un
  ext k
  fin_cases k
  · exact c0
  · exact c1

/-- A line transverse to the first ray is encountered at most once in a short
oriented fan. The half-turn condition selects just one ray of that line. -/
theorem eq_indices_of_inner_zero_short_fan {n : ℕ} (ray : Fin (n + 2) → Plane)
    (genuine : ∀ i, ray i ≠ 0)
    (nonzero : ∀ i : Fin (n + 1), orient 0 (ray i.castSucc) (ray i.succ) ≠ 0)
    (consistent : ∀ i : Fin (n + 1),
      (0 < orient 0 (ray i.castSucc) (ray i.succ)) ↔
        0 < orient 0 (ray (0 : Fin (n + 1)).castSucc) (ray (0 : Fin (n + 1)).succ))
    (short : (∑ i : Fin (n + 1), angle (ray i.castSucc) (ray i.succ)) ≤ Real.pi)
    {u : Plane} (transverse : inner ℝ u (ray 0) ≠ 0)
    {i j : Fin (n + 2)} (hi : inner ℝ u (ray i) = 0) (hj : inner ℝ u (ray j) = 0) :
    i = j := by
  have un : u ≠ 0 := by
    intro eq
    apply transverse
    rw [eq, inner_zero_left]
  obtain ⟨t, ray_eq⟩ := exists_lineMap_of_orient_eq_zero (genuine i).symm
    (orient_zero_of_orthogonal_pair un hi hj)
  rw [AffineMap.lineMap_apply_module'] at ray_eq
  simp only [sub_zero, add_zero] at ray_eq
  have tn : t ≠ 0 := by
    intro zero
    apply genuine j
    rw [ray_eq, zero, zero_smul]
  have offset : orient 0 (ray 0) (ray i) ≠ 0 := by
    intro collinear
    obtain ⟨s, at_s⟩ := exists_lineMap_of_orient_eq_zero (genuine 0).symm collinear
    rw [AffineMap.lineMap_apply_module'] at at_s
    simp only [sub_zero, add_zero] at at_s
    have sn : s ≠ 0 := by
      intro zero
      apply genuine i
      rw [at_s, zero, zero_smul]
    rw [at_s, real_inner_smul_right] at hi
    exact (mul_ne_zero sn transverse) hi
  let s := orient 0 (ray (0 : Fin (n + 1)).castSucc) (ray (0 : Fin (n + 1)).succ)
  have half := orient_mul_nonneg_of_sum_ray_angles_le_pi ray (genuine 0) nonzero consistent short
  have positive : 0 < orient 0 (ray 0) (ray i) * s :=
    lt_of_le_of_ne (half i) (mul_ne_zero offset (nonzero 0)).symm
  have dot_scale : orient 0 (ray 0) (ray j) = t * orient 0 (ray 0) (ray i) := by
    rw [ray_eq]
    simp only [orient, PiLp.zero_apply, sub_zero, PiLp.smul_apply, smul_eq_mul]
    ring
  have h := half j
  change 0 ≤ orient 0 (ray 0) (ray j) * s at h
  rw [dot_scale, mul_assoc] at h
  have tp := lt_of_le_of_ne (nonneg_of_mul_nonneg_left h positive) tn.symm
  apply (strictMono_angle_first_of_short_fan ray genuine nonzero consistent short).injective
  change angle (ray 0) (ray i) = angle (ray 0) (ray j)
  rw [ray_eq, angle_smul_right_of_pos _ _ tp]

end Unfoldings
