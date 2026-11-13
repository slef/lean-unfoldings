module

public import Unfoldings.Roof.HeightContinuity
public import Unfoldings.Roof.Topology
public import Unfoldings.Geometry.AffineEnvelope
public import Mathlib.Topology.Order.Compact

/-! Four distant support planes make an arbitrary-rim roof proper without changing old faces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Four affine planes forming a downward tent; their height parameter can be chosen freely. -/
def tentSupport (H L : ℝ) (s : Bool × Bool) : Plane →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ Plane H - L •
    ((if s.1 then (EuclideanSpace.proj 0).toLinearMap.toAffineMap
      else -(EuclideanSpace.proj 0).toLinearMap.toAffineMap) +
     (if s.2 then (EuclideanSpace.proj 1).toLinearMap.toAffineMap
      else -(EuclideanSpace.proj 1).toLinearMap.toAffineMap))

@[simp] theorem tentSupport_apply (H L : ℝ) (s : Bool × Bool) (p : Plane) :
    tentSupport H L s p = H - L *
      ((if s.1 then p 0 else -p 0) + (if s.2 then p 1 else -p 1)) := by
  rcases s with ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-- Every old support retains its label; the four new labels are disjoint from old faces. -/
def tentCompletionSupport (H L : ℝ) : Face ⊕ (Bool × Bool) → Plane →ᵃ[ℝ] ℝ :=
  Sum.elim K.supportHeight (tentSupport H L)

/-- The actual finite supporting-plane extension after adding the tent. -/
def tentCompletionHeight (H L : ℝ) : Plane → ℝ :=
  AffineEnvelope.height (K.tentCompletionSupport H L)

/-- Horizontal sections of the completed roof. -/
def tentCompletionClip (H L Z : ℝ) : Set Plane :=
  AffineEnvelope.clip (K.tentCompletionSupport H L) Z

theorem tentCompletionHeight_le_roofHeight (H L : ℝ) (p : Plane) :
    K.tentCompletionHeight H L p ≤ K.roofHeight p := by
  obtain ⟨f, equal⟩ := K.exists_roofHeight_eq_supportHeight p
  exact (AffineEnvelope.height_le (K.tentCompletionSupport H L) p (.inl f)).trans_eq equal.symm

theorem exists_tentSupport_eq (H L : ℝ) (p : Plane) :
    ∃ s : Bool × Bool, tentSupport H L s p = H - L * (|p 0| + |p 1|) := by
  by_cases first : 0 ≤ p 0 <;> by_cases last : 0 ≤ p 1
  · exact ⟨(true, true), by simp only [tentSupport_apply, ite_true,
      abs_of_nonneg first, abs_of_nonneg last]⟩
  · exact ⟨(true, false), by simp only [tentSupport_apply, ite_true, Bool.false_eq_true,
      ite_false, abs_of_nonneg first, abs_of_neg (lt_of_not_ge last)]⟩
  · exact ⟨(false, true), by simp only [tentSupport_apply, Bool.false_eq_true, ite_false,
      ite_true, abs_of_neg (lt_of_not_ge first), abs_of_nonneg last]⟩
  · exact ⟨(false, false), by simp only [tentSupport_apply, Bool.false_eq_true, ite_false,
      abs_of_neg (lt_of_not_ge first), abs_of_neg (lt_of_not_ge last)]⟩

theorem tent_lower_le_support (H : ℝ) {L : ℝ} (nonnegative : 0 ≤ L)
    (s : Bool × Bool) (p : Plane) :
    H - L * (|p 0| + |p 1|) ≤ tentSupport H L s p := by
  rw [tentSupport_apply]
  have bound : (if s.1 then p 0 else -p 0) + (if s.2 then p 1 else -p 1) ≤
      |p 0| + |p 1| := by
    apply add_le_add
    · split
      · exact le_abs_self _
      · exact neg_le_abs _
    · split
      · exact le_abs_self _
      · exact neg_le_abs _
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left bound nonnegative) H

theorem tentCompletionHeight_le_tent (H L : ℝ) (p : Plane) :
    K.tentCompletionHeight H L p ≤ H - L * (|p 0| + |p 1|) := by
  obtain ⟨s, equal⟩ := exists_tentSupport_eq H L p
  exact (AffineEnvelope.height_le (K.tentCompletionSupport H L) p (.inr s)).trans_eq equal

/-- The new support planes can all be made strictly inactive on the entire original roof. -/
theorem exists_tent_height (L : ℝ) :
    ∃ H : ℝ, ∀ p ∈ K.footprint, K.roofHeight p < H - L * (|p 0| + |p 1|) := by
  have continuous : Continuous (fun p : Plane => K.roofHeight p + L * (|p 0| + |p 1|)) := by
    exact K.continuous_roofHeight.add
      (continuous_const.mul (((EuclideanSpace.proj 0).continuous.abs).add
        ((EuclideanSpace.proj 1).continuous.abs)))
  obtain ⟨b, bound⟩ := K.compact_footprint.bddAbove_image continuous.continuousOn
  refine ⟨b + 1, ?_⟩
  intro p member
  have upper := bound ⟨p, member, rfl⟩
  linarith

/-- Inactive tent planes preserve every original face point and every original height. -/
theorem tentCompletionHeight_eq_on_footprint {H L : ℝ} (nonnegative : 0 ≤ L)
    (inactive : ∀ p ∈ K.footprint, K.roofHeight p < H - L * (|p 0| + |p 1|))
    {p : Plane} (member : p ∈ K.footprint) :
    K.tentCompletionHeight H L p = K.roofHeight p := by
  apply le_antisymm (K.tentCompletionHeight_le_roofHeight H L p)
  obtain ⟨i, equal⟩ := AffineEnvelope.exists_height_eq (K.tentCompletionSupport H L) p
  change K.roofHeight p ≤ AffineEnvelope.height (K.tentCompletionSupport H L) p
  rw [equal]
  cases i with
  | inl f => exact K.roofHeight_le_supportHeight p f
  | inr s => exact (inactive p member).le.trans (tent_lower_le_support H nonnegative s p)

end Unfoldings.ConvexRoof
