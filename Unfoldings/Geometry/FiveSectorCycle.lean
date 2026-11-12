module

public import Unfoldings.Geometry.FiveSectorInteriors
public import Unfoldings.Geometry.ComplexArea

/-! The five acute sectors have their actual cyclic ray order and make one full turn. -/

@[expose] public section

noncomputable section

namespace Unfoldings

def fiveSectorCycle : Fin 5 ≃ FiveSector where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr false, Sum.inr true]
  invFun
    | Sum.inl k => ⟨k.val, by have := k.isLt; omega⟩
    | Sum.inr upper => if upper then 4 else 3
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by
    cases k with
    | inl k => fin_cases k <;> rfl
    | inr upper => cases upper <;> rfl

theorem fiveSectorCycle_last_eq_next_first (t : ℝ) (k : Fin 5) :
    fiveSectorLast t (fiveSectorCycle k) =
      fiveSectorFirst t (fiveSectorCycle (finRotate 5 k)) := by
  fin_cases k <;> rfl

def fiveSectorAngularFan (t : ℝ) (positive : 0 < t) (small : t < 1) : AngularFan 4 where
  angle k := InnerProductGeometry.angle (fiveSectorFirst t (fiveSectorCycle k))
    (fiveSectorLast t (fiveSectorCycle k))
  positive k := by
    by_contra not_positive
    have zero := le_antisymm (not_lt.mp not_positive) (InnerProductGeometry.angle_nonneg _ _)
    obtain ⟨_, a, _, scaled⟩ := InnerProductGeometry.angle_eq_zero_iff.mp zero
    have genuine := fiveSector_banks_orient_pos positive small (fiveSectorCycle k)
    have vanish : orient 0 (fiveSectorFirst t (fiveSectorCycle k))
        (a • fiveSectorFirst t (fiveSectorCycle k)) = 0 := by
      simp only [orient, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply, sub_zero]
      ring
    rw [scaled, vanish] at genuine
    exact (lt_irrefl _ genuine)
  small k := (fiveSector_width_lt_pi_div_two positive small (fiveSectorCycle k)).trans
    (by linarith [Real.pi_pos])

/-- The actual sector rays in the fixed standard complex coordinates. -/
def fiveSectorComplexRay (t : ℝ) (k : Fin 5) : ℂ :=
  Complex.orthonormalBasisOneI.repr.symm (fiveSectorFirst t (fiveSectorCycle k))

theorem fiveSectorComplexRay_angle {t : ℝ} (positive : 0 < t) (small : t < 1)
    (k : Fin 5) :
    InnerProductGeometry.angle (fiveSectorComplexRay t k)
        (fiveSectorComplexRay t (finRotate 5 k)) =
      (fiveSectorAngularFan t positive small).angle k := by
  dsimp only [fiveSectorComplexRay]
  rw [← fiveSectorCycle_last_eq_next_first]
  exact (Complex.orthonormalBasisOneI.repr.symm.toLinearIsometry.angle_map _ _)

theorem fiveSectorComplexRay_cross_pos {t : ℝ} (positive : 0 < t) (small : t < 1)
    (k : Fin 5) :
    0 < (starRingEnd ℂ (fiveSectorComplexRay t k) *
      fiveSectorComplexRay t (finRotate 5 k)).im := by
  have area := orient_complex_repr_zero (fiveSectorComplexRay t k)
    (fiveSectorComplexRay t (finRotate 5 k))
  rw [show Complex.orthonormalBasisOneI.repr (fiveSectorComplexRay t k) =
    fiveSectorFirst t (fiveSectorCycle k) from
      Complex.orthonormalBasisOneI.repr.apply_symm_apply _] at area
  rw [show Complex.orthonormalBasisOneI.repr (fiveSectorComplexRay t (finRotate 5 k)) =
    fiveSectorFirst t (fiveSectorCycle (finRotate 5 k)) from
      Complex.orthonormalBasisOneI.repr.apply_symm_apply _] at area
  rw [← fiveSectorCycle_last_eq_next_first] at area
  rw [← area]
  exact fiveSector_banks_orient_pos positive small (fiveSectorCycle k)

theorem fiveSectorComplexRay_heading {t : ℝ} (positive : 0 < t) (small : t < 1)
    (k : Fin 5) :
    fiveSectorComplexRay t k = (‖fiveSectorComplexRay t k‖ : ℂ) *
      polarRay ((fiveSectorComplexRay t 0).arg +
        (fiveSectorAngularFan t positive small).heading k.castSucc) :=
  (fiveSectorAngularFan t positive small).cyclic_ray_heading (fiveSectorComplexRay t)
    (fiveSectorComplexRay_angle positive small) (fiveSectorComplexRay_cross_pos positive small) k

theorem fiveSectorAngularFan_totalAngle {t : ℝ} (positive : 0 < t) (small : t < 1) :
    (fiveSectorAngularFan t positive small).totalAngle = 2 * Real.pi := by
  let A := fiveSectorAngularFan t positive small
  let ray := fiveSectorComplexRay t
  have angles := fiveSectorComplexRay_angle positive small
  have cross := fiveSectorComplexRay_cross_pos positive small
  apply A.totalAngle_eq_two_pi_of_cyclic_rays ray angles cross
  intro k l different
  apply Set.disjoint_left.mpr
  intro x first last
  have first_cone := first
  have last_cone := last
  rcases first_cone with ⟨a, apos, b, bpos, equal⟩
  rcases last_cone with ⟨c, cpos, d, dpos, other⟩
  have first_physical : Complex.orthonormalBasisOneI.repr x ∈
      strictFiveSector t (fiveSectorCycle k) := by
    apply strictRayCone_subset_strictFiveSector positive small (fiveSectorCycle k)
    refine ⟨a, apos, b, bpos, ?_⟩
    rw [equal, map_add, map_smul, map_smul]
    simp only [ray, fiveSectorComplexRay, LinearIsometryEquiv.apply_symm_apply]
    rw [← fiveSectorCycle_last_eq_next_first]
  have last_physical : Complex.orthonormalBasisOneI.repr x ∈
      closedFiveSector t (fiveSectorCycle l) := by
    refine ⟨c, d, cpos.le, dpos.le, ?_⟩
    rw [other, map_add, map_smul, map_smul]
    simp only [ray, fiveSectorComplexRay, LinearIsometryEquiv.apply_symm_apply]
    rw [← fiveSectorCycle_last_eq_next_first]
  exact Set.disjoint_left.mp (strictFiveSector_disjoint_closed positive small
    (fun same => different (fiveSectorCycle.injective same))) first_physical last_physical

end Unfoldings
