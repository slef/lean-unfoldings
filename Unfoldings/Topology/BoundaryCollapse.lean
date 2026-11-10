module

public import Unfoldings.Topology.BoundaryQuotient
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Collapsing a closed boundary to the point at infinity

The complement embeds canonically in its one-point compactification. Send the
closed boundary to infinity and every other point to its own complement copy.
Continuity follows directly from the one-point topology: compact subsets of
the complement have closed images in the Hausdorff ambient space.
-/

@[expose] public section

open scoped OnePoint

noncomputable section

namespace Unfoldings

variable {X : Type*} (B : Set X)

def collapseBoundary (x : X) : OnePoint ↥(Bᶜ) := by
  classical
  exact if h : x ∈ B then ∞ else (⟨x, h⟩ : ↥(Bᶜ))

theorem collapseBoundary_of_mem {x : X} (inside : x ∈ B) : collapseBoundary B x = ∞ := by
  classical
  simp only [collapseBoundary, dite_eq_left inside]

@[simp] theorem collapseBoundary_of_not_mem {x : X} (outside : x ∉ B) :
    collapseBoundary B x = (⟨x, outside⟩ : ↥(Bᶜ)) := by
  classical
  simp only [collapseBoundary, dite_eq_right outside]

theorem collapseBoundary_fibers (x y : X) :
    collapseBoundary B x = collapseBoundary B y ↔ x = y ∨ (x ∈ B ∧ y ∈ B) := by
  constructor
  · intro equal
    by_cases hx : x ∈ B
    · by_cases hy : y ∈ B
      · exact Or.inr ⟨hx, hy⟩
      · rw [collapseBoundary_of_mem B hx, collapseBoundary_of_not_mem B hy] at equal
        exact (OnePoint.infty_ne_coe _ equal).elim
    · by_cases hy : y ∈ B
      · rw [collapseBoundary_of_not_mem B hx, collapseBoundary_of_mem B hy] at equal
        exact (OnePoint.coe_ne_infty _ equal).elim
      · rw [collapseBoundary_of_not_mem B hx, collapseBoundary_of_not_mem B hy] at equal
        exact Or.inl (congrArg Subtype.val (OnePoint.coe_injective equal))
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · rw [collapseBoundary_of_mem B hx, collapseBoundary_of_mem B hy]

theorem collapseBoundary_surjective (nonempty : B.Nonempty) :
    Function.Surjective (collapseBoundary B) := by
  intro y
  induction y using OnePoint.rec with
  | infty =>
    obtain ⟨x, hx⟩ := nonempty
    exact ⟨x, collapseBoundary_of_mem B hx⟩
  | coe x => exact ⟨x.val, collapseBoundary_of_not_mem B x.property⟩

variable [TopologicalSpace X]

theorem continuous_collapseBoundary [T2Space X] (closed : IsClosed B) :
    Continuous (collapseBoundary B) := by
  rw [continuous_def]
  intro U open_U
  by_cases infinity : (∞ : OnePoint ↥(Bᶜ)) ∈ U
  · have compact := (OnePoint.isOpen_def.mp open_U).1 infinity
    have equality : (collapseBoundary B ⁻¹' U)ᶜ =
        Subtype.val '' (((↑) : ↥(Bᶜ) → OnePoint ↥(Bᶜ)) ⁻¹' U)ᶜ := by
      ext x
      constructor
      · intro absent
        change collapseBoundary B x ∉ U at absent
        have outside : x ∉ B := by
          intro inside
          rw [collapseBoundary_of_mem B inside] at absent
          exact absent infinity
        exact ⟨⟨x, outside⟩, by
          change (↑(⟨x, outside⟩ : ↥(Bᶜ)) : OnePoint ↥(Bᶜ)) ∉ U
          simpa only [collapseBoundary_of_not_mem B outside] using absent, rfl⟩
      · rintro ⟨x, absent, rfl⟩
        change collapseBoundary B x.val ∉ U
        rwa [collapseBoundary_of_not_mem B x.property]
    have closed_compl : IsClosed (collapseBoundary B ⁻¹' U)ᶜ := by
      rw [equality]
      exact (compact.image continuous_subtype_val).isClosed
    exact isClosed_compl_iff.mp closed_compl
  · have equality : collapseBoundary B ⁻¹' U =
        Subtype.val '' (((↑) : ↥(Bᶜ) → OnePoint ↥(Bᶜ)) ⁻¹' U) := by
      ext x
      constructor
      · intro member
        change collapseBoundary B x ∈ U at member
        have outside : x ∉ B := by
          intro inside
          exact infinity ((collapseBoundary_of_mem B inside) ▸ member)
        exact ⟨⟨x, outside⟩, by
          change (↑(⟨x, outside⟩ : ↥(Bᶜ)) : OnePoint ↥(Bᶜ)) ∈ U
          simpa only [collapseBoundary_of_not_mem B outside] using member, rfl⟩
      · rintro ⟨x, member, rfl⟩
        change collapseBoundary B x.val ∈ U
        rwa [collapseBoundary_of_not_mem B x.property]
    rw [equality]
    exact closed.isOpen_compl.isOpenMap_subtype_val _ (OnePoint.isOpen_def.mp open_U).2

def collapseBoundaryQuotient [CompactSpace X] [T2Space X] (closed : IsClosed B)
    (nonempty : B.Nonempty) : BoundaryQuotient X (OnePoint ↥(Bᶜ)) where
  projection := ⟨collapseBoundary B, continuous_collapseBoundary B closed⟩
  quotient := by
    let : LocallyCompactSpace ↥(Bᶜ) := closed.isOpen_compl.locallyCompactSpace
    exact Topology.IsQuotientMap.of_surjective_continuous
      (collapseBoundary_surjective B nonempty) (continuous_collapseBoundary B closed)
  boundary := B
  fibers x y equal := (collapseBoundary_fibers B x y).mp equal

end Unfoldings
