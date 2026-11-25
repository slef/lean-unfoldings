module

public import Unfoldings.Geometry.PolygonalRaySuffix
public import Unfoldings.Geometry.BankCircleDirection
public import Unfoldings.Geometry.OpeningCommonDirection

/-! A common strict acute cone controls complete polygonal bank rays and all their suffixes. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real
open scoped NNReal

/-- The open right-angle cone about `center`, together with the zero vector. -/
def acuteBankCone (center : ℝ) : Set ℂ :=
  {z | z = 0 ∨ |(complexRotation (-center) z).im| < (complexRotation (-center) z).re}

namespace acuteBankCone

@[simp] theorem zero_mem (center : ℝ) : (0 : ℂ) ∈ acuteBankCone center := Or.inl rfl

theorem add_mem {center : ℝ} {x y : ℂ} (hx : x ∈ acuteBankCone center)
    (hy : y ∈ acuteBankCone center) : x + y ∈ acuteBankCone center := by
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · simp
  · rw [zero_add]
    exact Or.inr hy
  · rw [add_zero]
    exact Or.inr hx
  · right
    rw [map_add, Complex.add_im, Complex.add_re]
    exact (abs_add_le _ _).trans_lt (add_lt_add hx hy)

theorem smul_mem {center t : ℝ} {x : ℂ} (ht : 0 ≤ t)
    (hx : x ∈ acuteBankCone center) : t • x ∈ acuteBankCone center := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  rcases hx with rfl | hx
  · simp
  · right
    rw [map_smul]
    simp only [Complex.real_smul, Complex.mul_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero,
      abs_mul, abs_of_pos ht]
    exact mul_lt_mul_of_pos_left hx ht

/-- Literal real headings within a quarter-turn of the bisector lie in the strict cone. -/
theorem polarRay_mem {center h : ℝ} (within : |h - center| < π / 4) :
    polarRay h ∈ acuteBankCone center := by
  right
  rw [complexRotation_apply, ← polarRay_add, polarRay_re, polarRay_im]
  have bounds := abs_lt.mp within
  have arg : -center + h = h - center := by ring
  rw [arg]
  have cos_positive : 0 < cos (h - center) :=
    cos_pos_of_mem_Ioo ⟨by linarith only [bounds.1, pi_pos],
      by linarith only [bounds.2, pi_pos]⟩
  have double_positive : 0 < cos (2 * (h - center)) :=
    cos_pos_of_mem_Ioo ⟨by linarith only [bounds.1], by linarith only [bounds.2]⟩
  rw [cos_two_mul] at double_positive
  apply (sq_lt_sq₀ (abs_nonneg _) cos_positive.le).mp
  rw [sq_abs]
  linarith only [double_positive, sin_sq_add_cos_sq (h - center)]

/-- Every two nonzero directions in the same strict acute cone have positive inner product. -/
theorem inner_pos {center : ℝ} {x y : ℂ} (hx : x ∈ acuteBankCone center)
    (hy : y ∈ acuteBankCone center) (nx : x ≠ 0) (ny : y ≠ 0) : 0 < inner ℝ x y := by
  let L := complexRotation (-center)
  have xbound : |(L x).im| < (L x).re := hx.resolve_left nx
  have ybound : |(L y).im| < (L y).re := hy.resolve_left ny
  obtain ⟨xl, xr⟩ := abs_lt.mp xbound
  obtain ⟨yl, yr⟩ := abs_lt.mp ybound
  rw [← L.inner_map_map]
  rw [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  have lower := mul_pos (show 0 < (L x).re + (L x).im by linarith only [xl])
    (show 0 < (L y).re + (L y).im by linarith only [yl])
  have upper := mul_pos (show 0 < (L x).re - (L x).im by linarith only [xr])
    (show 0 < (L y).re - (L y).im by linarith only [yr])
  nlinarith only [lower, upper]

theorem inner_nonneg {center : ℝ} {x y : ℂ} (hx : x ∈ acuteBankCone center)
    (hy : y ∈ acuteBankCone center) : 0 ≤ inner ℝ x y := by
  by_cases nx : x = 0
  · simp [nx]
  by_cases ny : y = 0
  · simp [ny]
  exact (inner_pos hx hy nx ny).le

end acuteBankCone

namespace PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n)

/-- The complete bank, including the true tail, takes its steps in a single cone. -/
def InAcuteCone (center : ℝ) : Prop :=
  (∀ i, R.chain.edge i ∈ acuteBankCone center) ∧ R.direction ∈ acuteBankCone center

/-- All source-relative polygonal points stay in the cone of the rays' steps. -/
theorem InAcuteCone.displacement_mem {center : ℝ} (h : R.InAcuteCone center)
    {p : ℂ} (hp : p ∈ R.carrier) : p - R.start ∈ acuteBankCone center := by
  have vertex (j : Fin (n + 1)) : R.chain.vertex j - R.start ∈ acuteBankCone center := by
    apply Fin.induction (motive := fun j => R.chain.vertex j - R.start ∈ acuteBankCone center)
    · change R.start - R.start ∈ _
      rw [sub_self]
      exact acuteBankCone.zero_mem center
    · intro i prev
      rw [show R.chain.vertex i.succ - R.start =
          (R.chain.vertex i.castSucc - R.start) + R.chain.edge i by
        unfold PolygonalChain.edge
        abel]
      exact acuteBankCone.add_mem prev (h.1 i)
  rcases hp with finite | tail
  · rw [R.chain.path_range] at finite
    rcases finite with source | links
    · rw [Set.mem_singleton_iff.mp source]
      exact vertex 0
    · obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp links
      rw [PolygonalChain.point, AffineMap.lineMap_apply_module']
      rw [show (t : ℝ) • (R.chain.vertex i.succ - R.chain.vertex i.castSucc) +
          R.chain.vertex i.castSucc - R.start =
            (R.chain.vertex i.castSucc - R.start) + (t : ℝ) • R.chain.edge i by
        unfold PolygonalChain.edge
        abel]
      exact acuteBankCone.add_mem (vertex i.castSucc)
        (acuteBankCone.smul_mem t.property.1 (h.1 i))
  · obtain ⟨t, rfl⟩ := tail
    rw [PolygonalRay.tail, add_sub_right_comm]
    exact acuteBankCone.add_mem (vertex _) (acuteBankCone.smul_mem t.coe_nonneg h.2)

/-- The suffix at any hinge is radially nondecreasing, including its true infinite continuation. -/
theorem InAcuteCone.suffix {center : ℝ} (h : R.InAcuteCone center) (i : Fin (n + 1)) :
    (R.suffix i).InAcuteCone center := by
  refine ⟨fun j => ?_, h.2⟩
  change (R.chain.interval i.val (n - i.val) (by omega)).edge j ∈ _
  exact h.1 ⟨i.val + j.val, by omega⟩

theorem InAcuteCone.outward {center : ℝ} (h : R.InAcuteCone center) : R.Outward := by
  have outward : R.chain.Outward :=
    (PolygonalChain.PairwiseNonnegativeEdges.outward R.chain
      (fun i j => acuteBankCone.inner_nonneg (h.1 i) (h.1 j)))
  refine ⟨fun i hi => (R.chain.radiallyMonotone_iff_outward.mpr outward) 0 i hi, ?_⟩
  have endpoint : R.chain.vertex (Fin.last n) ∈ R.carrier := by
    simpa only [R.tail_zero] using R.tail_mem 0
  exact acuteBankCone.inner_nonneg (h.displacement_mem R endpoint) h.2

/-- On a positive source circle, any two banks in the common cone remain in the
same open halfplane relative to one another. -/
theorem circleDirection_div_re_pos_of_acuteCone {m : ℕ} (Q : PolygonalRay ℂ m)
    {center : ℝ} (first : R.InAcuteCone center) (second : Q.InAcuteCone center)
    (r : ℝ≥0) (positive : 0 < r) (nonzeroR : R.direction ≠ 0) (nonzeroQ : Q.direction ≠ 0) :
    0 < ((Q.circleDirection (second.outward Q) nonzeroQ r positive /
      R.circleDirection (first.outward R) nonzeroR r positive : Circle) : ℂ).re := by
  let p := R.radialPoint (first.outward R) nonzeroR r - R.start
  let q := Q.radialPoint (second.outward Q) nonzeroQ r - Q.start
  have hp := first.displacement_mem R (R.radialPoint_mem (first.outward R) nonzeroR r)
  have hq := second.displacement_mem Q (Q.radialPoint_mem (second.outward Q) nonzeroQ r)
  have np : p ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [show ‖p‖ = r from R.norm_radialPoint_sub_start _ _ _]
    exact (show (0 : ℝ) < r from positive).ne'
  have nq : q ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [show ‖q‖ = r from Q.norm_radialPoint_sub_start _ _ _]
    exact (show (0 : ℝ) < r from positive).ne'
  have actual : 0 < inner ℝ p q := acuteBankCone.inner_pos hp hq np nq
  rw [Circle.coe_div, Q.circleDirection_coe, R.circleDirection_coe]
  change 0 < (q / (r : ℂ) / (p / (r : ℂ))).re
  have rne := Complex.ofReal_ne_zero.mpr (show (0 : ℝ) < r from positive).ne'
  have cancel : q / (r : ℂ) / (p / (r : ℂ)) = q / p := by field_simp
  rw [cancel]
  exact complex_div_re_pos_of_inner_pos actual

end PolygonalRay
end Unfoldings
