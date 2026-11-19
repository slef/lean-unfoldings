module

public import Mathlib.Data.Set.Finite.Basic

/-! Extend a finite-fiber boundary label by retaining each remaining point's original tag. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {X A Tag : Type*} (boundary : Set X) (label : boundary → A) (tag : Tag)

/-- Boundary points retain their physical labels; all other points retain their original copy. -/
def partialLabel (x : X) : A ⊕ (Tag × X) := by
  classical
  exact if member : x ∈ boundary then .inl (label ⟨x, member⟩) else .inr (tag, x)

/-- Every actual boundary point keeps its original physical label. -/
theorem partialLabel_of_mem (x : X) (member : x ∈ boundary) :
    partialLabel boundary label tag x = .inl (label ⟨x, member⟩) := by
  unfold partialLabel
  split
  · rfl
  · rename_i absent
    exact (absent member).elim

/-- Retaining the remaining original point tags preserves finite fibers. -/
theorem finite_partialLabel_fiber (finite : ∀ a, {x : boundary | label x = a}.Finite)
    (value : A ⊕ (Tag × X)) : {x : X | partialLabel boundary label tag x = value}.Finite := by
  classical
  cases value with
  | inl a =>
    apply ((finite a).image Subtype.val).subset
    intro x named
    change partialLabel boundary label tag x = .inl a at named
    by_cases member : x ∈ boundary
    · refine ⟨⟨x, member⟩, ?_, rfl⟩
      exact Sum.inl.inj ((partialLabel_of_mem boundary label tag x member).symm.trans named)
    · unfold partialLabel at named
      split at named
      · rename_i present
        exact (member present).elim
      · contradiction
  | inr p =>
    apply (Set.finite_singleton p.2).subset
    intro x named
    change partialLabel boundary label tag x = .inr p at named
    by_cases member : x ∈ boundary
    · have impossible := (partialLabel_of_mem boundary label tag x member).symm.trans named
      contradiction
    · unfold partialLabel at named
      split at named
      · rename_i present
        exact (member present).elim
      · exact congrArg Prod.snd (Sum.inr.inj named)

end Unfoldings.MetricGluing
