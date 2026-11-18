module

public import Unfoldings.Complex.SurvivingBoundaryChain
public import Unfoldings.Complex.BoundaryChainTrace

/-! Untouched surviving bank sides retain their complete closed metric traces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam} (inclusion : small ⊆ large) {n : ℕ}
  (chain : (C.boundarySystem small).Chain n)
  (survives : ∀ i, C.IsBoundaryEdge large (C.germEdge (chain.point i).val))

@[simp] theorem survivingBoundaryChain_point (i : Fin (n + 1)) :
    (C.survivingBoundaryChain inclusion chain survives).point i =
      C.survivingBoundaryEnd (chain.point i) (survives i) := rfl

/-- Turning a surviving bank uses the same original far germ in either cut surface. -/
theorem survivingBoundaryEnd_turn_germ (p : C.BoundaryEnd small)
    (kept : C.IsBoundaryEdge large (C.germEdge p.val)) :
    (C.boundaryTurn large (C.survivingBoundaryEnd p kept)).val =
      (C.boundaryTurn small p).val := by
  obtain ⟨⟨bank, side⟩, rfl⟩ := (C.boundaryEndEquiv small).symm.surjective p
  rcases bank with ⟨⟨face, edge⟩, boundary⟩
  cases side <;> fin_cases edge <;> rfl

/-- Original metric copies and every point on each closed bank survive the restoration map. -/
theorem survivingBoundaryChain_trace :
    C.boundaryChainTrace (C.survivingBoundaryChain inclusion chain survives) =
      C.forgetCuts inclusion '' C.boundaryChainTrace chain := by
  rw [C.boundaryChainTrace_eq_union_paths, C.boundaryChainTrace_eq_union_paths,
    Set.image_iUnion]
  apply Set.iUnion_congr
  intro i
  rw [← Set.range_comp]
  apply congrArg Set.range
  funext t
  exact C.survivingBoundaryEnd_path inclusion (chain.point i) (survives i) t

end Unfoldings.TriangleComplex
