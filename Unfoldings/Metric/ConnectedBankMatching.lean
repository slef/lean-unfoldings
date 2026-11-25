module

public import Mathlib.Topology.MetricSpace.Dilation
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.UniformSpace.Real

/-! The two closed banks of an isolated ray have locally constant labels along any lift. -/

@[expose] public section

open scoped NNReal

namespace Unfoldings.MetricGluing

variable {X A : Type*} [EMetricSpace X] [TopologicalSpace A]

/-- Every connected curve of positive points from two disjoint closed
banks follows a fixed bank, including according to the given parametrization. -/
theorem exists_bank_side_of_preconnected [PreconnectedSpace A]
    (bank : Bool → ℝ≥0 →ᵈ X)
    (apart : ∀ side other : Bool, side ≠ other → ∀ s t, 0 < s.val → bank side s ≠ bank other t)
    (curve : A → X) (continuous : Continuous curve) (time : A → ℝ≥0)
    (positive : ∀ a, 0 < (time a).val)
    (covered : ∀ a, ∃ side, curve a = bank side (time a)) :
    ∃ side, ∀ a, curve a = bank side (time a) := by
  let region (side : Bool) := curve ⁻¹' Set.range (bank side)
  have closed (side : Bool) : IsClosed (region side) :=
    (Dilation.isClosedEmbedding (bank side)).isClosed_range.preimage continuous
  have cover : Set.univ ⊆ region false ∪ region true := by
    intro a _
    obtain ⟨side, same⟩ := covered a
    cases side
    · exact Or.inl ⟨time a, same.symm⟩
    · exact Or.inr ⟨time a, same.symm⟩
  have same_side (a : A) (side : Bool) (member : a ∈ region side) :
      curve a = bank side (time a) := by
    obtain ⟨t, ht⟩ := member
    obtain ⟨actual, ha⟩ := covered a
    by_contra different
    have labels : actual ≠ side := fun h => different (h ▸ ha)
    exact (apart actual side labels (time a) t (positive a)) (ha.symm.trans ht.symm)
  have disjoint : Disjoint (region false) (region true) := by
    apply Set.disjoint_left.mpr
    intro a first last
    exact (apart false true (by decide) (time a) (time a) (positive a))
      ((same_side a false first).symm.trans (same_side a true last))
  by_cases left : (region false).Nonempty
  · refine ⟨false, fun a => same_side a false ?_⟩
    rcases cover (Set.mem_univ a) with member | member
    · exact member
    · obtain ⟨b, hb⟩ := left
      obtain ⟨c, _, first, last⟩ := isPreconnected_closed_iff.mp isPreconnected_univ
        (region false) (region true) (closed false) (closed true) cover
        ⟨b, Set.mem_univ b, hb⟩ ⟨a, Set.mem_univ a, member⟩
      exact False.elim (Set.disjoint_left.mp disjoint first last)
  · refine ⟨true, fun a => same_side a true ?_⟩
    rcases cover (Set.mem_univ a) with member | member
    · exact False.elim (left ⟨a, member⟩)
    · exact member

/-- Agreement on a dense connected positive part includes the
limiting bank endpoint. -/
theorem exists_bank_side_of_dense_positive
    (bank : Bool → ℝ≥0 →ᵈ X)
    (apart : ∀ side other : Bool, side ≠ other → ∀ s t, 0 < s.val → bank side s ≠ bank other t)
    (curve : A → X) (continuous : Continuous curve) (time : A → ℝ≥0)
    (continuous_time : Continuous time) (S : Set A) (connected : IsPreconnected S) (dense : Dense S)
    (positive : ∀ a ∈ S, 0 < (time a).val)
    (covered : ∀ a ∈ S, ∃ side, curve a = bank side (time a)) :
    ∃ side, ∀ a, curve a = bank side (time a) := by
  let : PreconnectedSpace S := Subtype.preconnectedSpace connected
  obtain ⟨side, same⟩ := exists_bank_side_of_preconnected bank apart
    (fun a : S => curve a.val) (continuous.comp continuous_subtype_val) (fun a : S => time a.val)
    (fun a => positive a.val a.property) (fun a => covered a.val a.property)
  have agrees : Set.EqOn curve (fun a => bank side (time a)) S := fun a ha => same ⟨a, ha⟩
  exact ⟨side, fun a => agrees.closure continuous
    ((Dilation.lipschitzWith (bank side)).continuous.comp continuous_time) (dense a)⟩

end Unfoldings.MetricGluing
