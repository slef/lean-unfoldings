module

public import Unfoldings.Geometry.CyclicRays

/-! Disjoint consecutive open cones keep the same orientation around their common ray. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

theorem strictRayCone_comm (x y : E) : strictRayCone x y = strictRayCone y x := by
  ext z
  constructor <;> rintro ⟨a, ha, b, hb, rfl⟩ <;> exact ⟨b, hb, a, ha, add_comm _ _⟩

theorem _root_.LinearMap.image_strictRayCone {F : Type*} [AddCommMonoid F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (x y : E) : L '' strictRayCone x y = strictRayCone (L x) (L y) := by
  ext z
  constructor
  · rintro ⟨w, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨a, ha, b, hb, by rw [map_add, map_smul, map_smul]⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a • x + b • y, ⟨a, ha, b, hb, rfl⟩, by rw [map_add, map_smul, map_smul]⟩

/-- A positive balance gives an actual point shared by both open cones. -/
theorem not_disjoint_strictRayCone_of_balance {x y z : E} {a b t : ℝ}
    (apos : 0 < a) (bpos : 0 < b) (balance : a • x = t • y + b • z) :
    ¬ Disjoint (strictRayCone x y) (strictRayCone y z) := by
  intro separated
  have lpos : 0 < |t| + 1 := by positivity
  have mpos : 0 < |t| + 1 + t := by linarith [neg_abs_le t]
  have first : a • x + (|t| + 1) • y ∈ strictRayCone x y := ⟨a, apos, _, lpos, rfl⟩
  have last : a • x + (|t| + 1) • y ∈ strictRayCone y z := by
    refine ⟨|t| + 1 + t, mpos, b, bpos, ?_⟩
    rw [balance]
    simp only [add_smul]
    module
  exact Set.disjoint_left.mp separated first last

/-- The planar determinant dependence of three vectors. -/
theorem complex_cross_balance (x y z : ℂ) :
    (starRingEnd ℂ y * z).im • x + (starRingEnd ℂ z * x).im • y +
      (starRingEnd ℂ x * y).im • z = 0 := by
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_re, Complex.zero_im] <;> ring

/-- Adjacent genuine cones with disjoint interiors must turn in the same direction. -/
theorem cross_mul_pos_of_disjoint_strictRayCones {x y z : ℂ}
    (first : (starRingEnd ℂ x * y).im ≠ 0) (last : (starRingEnd ℂ y * z).im ≠ 0)
    (separated : Disjoint (strictRayCone x y) (strictRayCone y z)) :
    0 < (starRingEnd ℂ x * y).im * (starRingEnd ℂ y * z).im := by
  have balance := complex_cross_balance x y z
  by_contra notpos
  have negative : (starRingEnd ℂ x * y).im * (starRingEnd ℂ y * z).im < 0 :=
    lt_of_le_of_ne (le_of_not_gt notpos) (mul_ne_zero first last)
  rcases lt_or_gt_of_ne first with left | right
  · have rightpos : 0 < (starRingEnd ℂ y * z).im := by
      rcases mul_neg_iff.mp negative with pair | pair
      · exact (left.not_gt pair.1).elim
      · exact pair.2
    have equation : (starRingEnd ℂ y * z).im • x =
        (-(starRingEnd ℂ z * x).im) • y + (-(starRingEnd ℂ x * y).im) • z := by
      apply Complex.ext
      · have real := congrArg Complex.re balance
        simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at real ⊢
        linarith
      · have imaginary := congrArg Complex.im balance
        simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] at imaginary ⊢
        linarith
    exact not_disjoint_strictRayCone_of_balance rightpos (neg_pos.mpr left) equation separated
  · have rightneg : (starRingEnd ℂ y * z).im < 0 := by
      rcases mul_neg_iff.mp negative with pair | pair
      · exact pair.2
      · exact (right.not_gt pair.1).elim
    have equation : (-(starRingEnd ℂ y * z).im) • x =
        (starRingEnd ℂ z * x).im • y + (starRingEnd ℂ x * y).im • z := by
      apply Complex.ext
      · have real := congrArg Complex.re balance
        simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at real ⊢
        linarith
      · have imaginary := congrArg Complex.im balance
        simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] at imaginary ⊢
        linarith
    exact not_disjoint_strictRayCone_of_balance (neg_pos.mpr rightneg) right equation separated

namespace AngularFan

variable {n : ℕ} (A : AngularFan n) (ray : Fin (n + 1) → ℂ)
  (angles : ∀ i, InnerProductGeometry.angle (ray i) (ray (finRotate (n + 1) i)) = A.angle i)
  (genuine : ∀ i, (starRingEnd ℂ (ray i) * ray (finRotate (n + 1) i)).im ≠ 0)
  (separated : Pairwise (fun i j => Disjoint
    (strictRayCone (ray i) (ray (finRotate (n + 1) i)))
    (strictRayCone (ray j) (ray (finRotate (n + 1) j)))))

include genuine separated in
/-- Consecutive disjoint genuine wedges have a common orientation, including cyclic closure. -/
theorem cyclic_cross_sign (i : Fin (n + 1)) :
    (0 < (starRingEnd ℂ (ray i) * ray (finRotate (n + 1) i)).im) ↔
      0 < (starRingEnd ℂ (ray 0) * ray (finRotate (n + 1) 0)).im := by
  refine Fin.induction Iff.rfl (fun k previous => ?_) i
  have different : k.castSucc ≠ finRotate (n + 1) k.castSucc := by
    intro equal
    have nonzero := genuine k.castSucc
    rw [← equal] at nonzero
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at nonzero
    exact nonzero (by ring)
  have product := cross_mul_pos_of_disjoint_strictRayCones
    (genuine k.castSucc) (genuine (finRotate (n + 1) k.castSucc)) (separated different)
  have rotated : finRotate (n + 1) k.castSucc = k.succ := finRotate_of_lt k.isLt
  rw [rotated] at product previous
  exact (pos_iff_pos_of_mul_pos product).symm.trans previous

include angles genuine separated in
/-- Reflection handles either orientation of the actual planar cyclic fan. -/
theorem totalAngle_eq_two_pi_of_disjoint_cyclic_rays : A.totalAngle = 2 * Real.pi := by
  by_cases initial : 0 < (starRingEnd ℂ (ray 0) * ray (finRotate (n + 1) 0)).im
  · exact A.totalAngle_eq_two_pi_of_cyclic_rays ray angles
      (fun i => (cyclic_cross_sign ray genuine separated i).mpr initial) separated
  · let L : ℂ ≃ₗᵢ[ℝ] ℂ := Complex.conjLIE
    have conjugate (x y : ℂ) :
        (starRingEnd ℂ (L x) * L y).im = -(starRingEnd ℂ x * y).im := by
      change (starRingEnd ℂ (starRingEnd ℂ x) * starRingEnd ℂ y).im = _
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    have positive (i : Fin (n + 1)) :
        0 < (starRingEnd ℂ (L (ray i)) * L (ray (finRotate (n + 1) i))).im := by
      rw [conjugate]
      apply neg_pos.mpr
      exact lt_of_le_of_ne (le_of_not_gt (fun hi =>
        initial ((cyclic_cross_sign ray genuine separated i).mp hi))) (genuine i)
    apply A.totalAngle_eq_two_pi_of_cyclic_rays (fun i => L (ray i))
      (fun i => (L.toLinearIsometry.angle_map _ _).trans (angles i)) positive
    intro i j different
    change Disjoint
      (strictRayCone (L.toLinearMap (ray i)) (L.toLinearMap (ray (finRotate (n + 1) i))))
      (strictRayCone (L.toLinearMap (ray j)) (L.toLinearMap (ray (finRotate (n + 1) j))))
    rw [← L.toLinearMap.image_strictRayCone, ← L.toLinearMap.image_strictRayCone]
    exact (Set.disjoint_image_iff L.injective).mpr (separated different)

end AngularFan
end Unfoldings
