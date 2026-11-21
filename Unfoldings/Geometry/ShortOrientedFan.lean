module

public import Unfoldings.Geometry.ComplexTurn
public import Unfoldings.Geometry.ComplexArea
public import Unfoldings.Geometry.PlanarConjugation
public import Unfoldings.Geometry.ChainConstruction

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

end Unfoldings
