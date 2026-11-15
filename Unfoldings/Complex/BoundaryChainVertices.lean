module

public import Unfoldings.Complex.BoundaryOrdering

/-! A finite actual boundary chain never repeats a starting cut-vertex copy. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) {n : ℕ} (chain : (C.boundarySystem retain).Chain n)

/-- Two starting ends of one actual chain cannot be mates at the same cut vertex. -/
theorem boundaryChain_point_ne_mate (i j : Fin (n + 1)) :
    chain.point i ≠ C.boundaryMate retain (chain.point j) := by
  refine Fin.cases ?_ (fun k equal => ?_) j
  · refine Fin.cases ?_ (fun k equal => ?_) i
    · intro equal
      exact (C.boundaryMate_spec retain (chain.point 0)).1 equal.symm
    · have opposite : chain.point 0 = C.boundaryMate retain (chain.point k.succ) := by
        rw [equal, C.boundaryMate_involutive]
      have previous := chain.mate_succ k
      change C.boundaryMate retain (chain.point k.succ) =
        C.boundaryTurn retain (chain.point k.castSucc) at previous
      rw [previous] at opposite
      exact chain.disjoint 0 k.castSucc opposite
  · have previous := chain.mate_succ k
    change C.boundaryMate retain (chain.point k.succ) =
      C.boundaryTurn retain (chain.point k.castSucc) at previous
    rw [previous] at equal
    exact chain.disjoint i k.castSucc equal

/-- Injectivity concerns intrinsic cut-vertex copies; projected vertices may overlap.
No cyclic closing or disk hypothesis is needed. -/
theorem boundaryChain_vertices_injective :
    Function.Injective (fun i => C.boundaryEndVertex retain (chain.point i)) := by
  intro i j same
  rcases (C.boundaryEnd_vertex_eq_iff retain _ _).mp same with equal | opposite
  · exact chain.injective equal
  · exact (C.boundaryChain_point_ne_mate retain chain i j opposite).elim

end Unfoldings.TriangleComplex
