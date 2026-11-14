module

public import Unfoldings.Topology.AscendingForest
public import Mathlib.Basic.Finite.Sum

/-! Extend a finite increasing forest by one new boundary leaf beyond each old root. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents

variable {V : Type*} (P : AscendingParents V)

/-- Old vertices and separately named new leaves, one for every old root. -/
abbrev LeafVertex := V ⊕ {v // v ∈ P.roots}

open Classical in
/-- Every old root acquires one outgoing edge. Precisely the new leaves are roots. -/
def withLeaves (level : ℝ) (higher : ∀ v, P.height v < level) :
    AscendingParents P.LeafVertex where
  roots := Set.range Sum.inr
  parent := fun v => match v with
    | .inl v => if root : v ∈ P.roots then .inr ⟨v, root⟩ else .inl (P.parent v)
    | .inr v => .inr v
  height := fun v => match v with
    | .inl v => P.height v
    | .inr _ => level
  fixed_root := by
    rintro _ ⟨v, rfl⟩
    rfl
  ascending := by
    intro v nonroot
    cases v with
    | inl v =>
      dsimp
      split_ifs with root
      · exact higher v
      · exact P.ascending v root
    | inr v => exact (nonroot ⟨v, rfl⟩).elim

variable (level : ℝ) (higher : ∀ v, P.height v < level)

@[simp] theorem withLeaves_inl_nonroot (v : V) :
    Sum.inl v ∉ (P.withLeaves level higher).roots := by
  rintro ⟨_, equal⟩
  cases equal

@[simp] theorem withLeaves_inr_root (v : {v // v ∈ P.roots}) :
    Sum.inr v ∈ (P.withLeaves level higher).roots := ⟨v, rfl⟩

theorem withLeaves_parent_nonroot {v : V} (nonroot : v ∉ P.roots) :
    (P.withLeaves level higher).parent (.inl v) = .inl (P.parent v) := by
  simp [withLeaves, nonroot]

theorem withLeaves_parent_root (v : {v // v ∈ P.roots}) :
    (P.withLeaves level higher).parent (.inl v.val) = .inr v := by
  simp [withLeaves, v.property]

variable [Finite V]

theorem withLeaves_rootedForest :
    (P.withLeaves level higher).graph.IsRootedForest (Set.range Sum.inr) :=
  (P.withLeaves level higher).graph_rootedForest

end Unfoldings.AscendingParents
