module

public import Unfoldings.Geometry.AffineOrientation
public import Unfoldings.Geometry.HalfplaneFan

/-! A nonsingular linear map sends a halfplane fan to another halfplane fan. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open InnerProductGeometry

theorem sum_linear_map_ray_angles_eq_endpoint {n : ℕ} (L : Plane ≃ₗ[ℝ] Plane)
    (ray : Fin (n + 2) → Plane) (genuine : ∀ i, ray i ≠ 0)
    (nonzero : ∀ i : Fin (n + 1), orient 0 (ray i.castSucc) (ray i.succ) ≠ 0)
    (consistent : ∀ i : Fin (n + 1),
      (0 < orient 0 (ray i.castSucc) (ray i.succ)) ↔
        0 < orient 0 (ray (0 : Fin (n + 1)).castSucc) (ray (0 : Fin (n + 1)).succ))
    (halfplane : ∀ i, 0 ≤ orient 0 (ray 0) (ray i) *
      orient 0 (ray (0 : Fin (n + 1)).castSucc) (ray (0 : Fin (n + 1)).succ)) :
    (∑ i : Fin (n + 1), angle (L (ray i.castSucc)) (L (ray i.succ))) =
      angle (L (ray 0)) (L (ray (Fin.last (n + 1)))) := by
  let s := orientationScale L.toLinearMap.toAffineMap
  have area (x y : Plane) : orient 0 (L x) (L y) = s * orient 0 x y :=
    orient_affine_linear L.toLinearMap.toAffineMap x y
  have sn : s ≠ 0 := by
    intro zero
    have eq := area (L.symm (EuclideanSpace.single 0 1)) (L.symm (EuclideanSpace.single 1 1))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, zero, zero_mul] at eq
    have basis_area : orient (0 : Plane) (EuclideanSpace.single 0 1)
        (EuclideanSpace.single 1 1) = 1 := by norm_num [orient]
    exact one_ne_zero (basis_area.symm.trans eq)
  refine sum_ray_angles_eq_endpoint (fun i => L (ray i)) ?_ ?_ ?_ ?_
  · intro i
    simpa only [map_zero] using L.injective.ne (genuine i)
  · intro i
    rw [area]
    exact mul_ne_zero sn (nonzero i)
  · intro i
    rw [area, area]
    rcases lt_or_gt_of_ne sn with neg | pos
    · simp only [mul_pos_iff, not_lt_of_ge neg.le, false_and, neg, true_and, false_or]
      have negative_iff (x : ℝ) (hx : x ≠ 0) : x < 0 ↔ ¬ 0 < x :=
        ⟨fun hn hp => (lt_asymm hn hp), fun h => lt_of_le_of_ne (le_of_not_gt h) hx⟩
      rw [negative_iff _ (nonzero i), negative_iff _ (nonzero 0)]
      exact not_congr (consistent i)
    · simpa only [mul_pos_iff_of_pos_left pos] using consistent i
  · intro i
    rw [area, area]
    calc
      _ = s ^ 2 * (orient 0 (ray 0) (ray i) *
          orient 0 (ray (0 : Fin (n + 1)).castSucc) (ray (0 : Fin (n + 1)).succ)) := by ring
      _ ≥ 0 := mul_nonneg (sq_nonneg s) (halfplane i)

end Unfoldings
