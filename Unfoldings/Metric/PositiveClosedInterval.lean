module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.UnitInterval

/-! Connected dense positive portions and actual nonnegative interpolation on closed intervals. -/

@[expose] public section

namespace Unfoldings

open scoped NNReal

theorem positiveIcc_image (T : ℝ) :
    Subtype.val '' {t : Set.Icc (0 : ℝ) T | 0 < t.val} = Set.Ioc (0 : ℝ) T := by
  ext t
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨hq, q.property.2⟩
  · intro ht
    exact ⟨⟨t, ht.1.le, ht.2⟩, ht.1, rfl⟩

theorem isPreconnected_positiveIcc (T : ℝ) :
    IsPreconnected {t : Set.Icc (0 : ℝ) T | 0 < t.val} := by
  apply Topology.IsEmbedding.subtypeVal.isInducing.isPreconnected_image.mp
  rw [positiveIcc_image]
  exact isPreconnected_Ioc

theorem dense_positiveIcc {T : ℝ} (positive : 0 < T) :
    Dense {t : Set.Icc (0 : ℝ) T | 0 < t.val} := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro t
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  change t.val ∈ closure (Subtype.val '' {t : Set.Icc (0 : ℝ) T | 0 < t.val})
  rw [positiveIcc_image, closure_Ioc positive.ne]
  exact t.property

/-- The actual nonnegative ray time at every point of a forward closed bank interval. -/
def nonnegativeIntervalLineMap (a b : ℝ) (nonnegative : 0 ≤ a) (forward : a ≤ b)
    (t : unitInterval) : ℝ≥0 :=
  ⟨a + t.val * (b - a), add_nonneg nonnegative (mul_nonneg t.property.1 (sub_nonneg.mpr forward))⟩

theorem continuous_nonnegativeIntervalLineMap (a b : ℝ) (nonnegative : 0 ≤ a) (forward : a ≤ b) :
    Continuous (nonnegativeIntervalLineMap a b nonnegative forward) :=
  (continuous_const.add (continuous_subtype_val.mul continuous_const)).subtype_mk _

/-- The same original ray times in their actual bounded closed parameter interval. -/
def closedNonnegativeIntervalLineMap (a b T : ℝ) (nonnegative : 0 ≤ a) (forward : a ≤ b)
    (before : b ≤ T) (t : unitInterval) : Set.Icc (0 : ℝ) T :=
  ⟨(nonnegativeIntervalLineMap a b nonnegative forward t).val,
    (nonnegativeIntervalLineMap a b nonnegative forward t).property,
    (by
      change a + t.val * (b - a) ≤ T
      nlinarith [mul_le_mul_of_nonneg_right t.property.2 (sub_nonneg.mpr forward)])⟩

theorem continuous_closedNonnegativeIntervalLineMap (a b T : ℝ) (nonnegative : 0 ≤ a)
    (forward : a ≤ b) (before : b ≤ T) :
    Continuous (closedNonnegativeIntervalLineMap a b T nonnegative forward before) :=
  (continuous_const.add (continuous_subtype_val.mul continuous_const)).subtype_mk _

/-- Every original time in the closed subinterval occurs in the exact affine parameterization. -/
theorem range_closedNonnegativeIntervalLineMap (a b T : ℝ) (nonnegative : 0 ≤ a)
    (forward : a < b) (before : b ≤ T) :
    Set.range (closedNonnegativeIntervalLineMap a b T nonnegative forward.le before) =
      {q : Set.Icc (0 : ℝ) T | a ≤ q.val ∧ q.val ≤ b} := by
  ext q
  constructor
  · rintro ⟨u, rfl⟩
    change a ≤ a + u.val * (b - a) ∧ a + u.val * (b - a) ≤ b
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg u.property.1 (sub_nonneg.mpr forward.le))
    · nlinarith [mul_le_mul_of_nonneg_right u.property.2 (sub_nonneg.mpr forward.le)]
  · intro hq
    have positive : 0 < b - a := sub_pos.mpr forward
    have lower : 0 ≤ (q.val - a) / (b - a) := div_nonneg (sub_nonneg.mpr hq.1) positive.le
    have upper : (q.val - a) / (b - a) ≤ 1 := (div_le_one positive).mpr (by linarith [hq.2])
    refine ⟨⟨(q.val - a) / (b - a), lower, upper⟩, Subtype.ext ?_⟩
    change a + ((q.val - a) / (b - a)) * (b - a) = q.val
    rw [div_mul_cancel₀ _ positive.ne']
    ring

end Unfoldings
