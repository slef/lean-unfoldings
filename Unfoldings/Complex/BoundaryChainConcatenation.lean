module

public import Unfoldings.Complex.BoundaryChainTrace
public import Unfoldings.Topology.ChainConcatRange

/-! Actual chain concatenation retains exactly both original bank traces. -/

@[expose] public section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam} {n m : ℕ} (a : (C.boundarySystem retain).Chain n)
  (b : (C.boundarySystem retain).Chain m)
  (separated : ∀ i j, a.point i ≠ b.point j ∧
    a.point i ≠ C.boundaryTurn retain (b.point j))
  (joined : C.boundaryMate retain (C.boundaryTurn retain a.last) = b.first)

/-- Joining two actual disjoint boundary chains retains both complete intrinsic traces. -/
theorem boundaryChainTrace_concat :
    C.boundaryChainTrace (a.concat b separated joined) =
      C.boundaryChainTrace a ∪ C.boundaryChainTrace b := by
  rw [C.boundaryChainTrace_eq_union_paths, C.boundaryChainTrace_eq_union_paths,
    C.boundaryChainTrace_eq_union_paths]
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_union]
  constructor
  · rintro ⟨i, u, at_point⟩
    rcases (a.concat_point_range_iff b separated joined _).mp ⟨i, rfl⟩ with
      ⟨j, named⟩ | ⟨j, named⟩
    · exact Or.inl ⟨j, u, (congrArg (fun p => C.directedBoundaryPath p u) named).trans at_point⟩
    · exact Or.inr ⟨j, u, (congrArg (fun p => C.directedBoundaryPath p u) named).trans at_point⟩
  · rintro (⟨i, u, at_point⟩ | ⟨j, u, at_point⟩)
    · obtain ⟨k, named⟩ := (a.concat_point_range_iff b separated joined _).mpr (Or.inl ⟨i, rfl⟩)
      exact ⟨k, u, (congrArg (fun p => C.directedBoundaryPath p u) named).trans at_point⟩
    · obtain ⟨k, named⟩ := (a.concat_point_range_iff b separated joined _).mpr (Or.inr ⟨j, rfl⟩)
      exact ⟨k, u, (congrArg (fun p => C.directedBoundaryPath p u) named).trans at_point⟩

end Unfoldings.TriangleComplex
