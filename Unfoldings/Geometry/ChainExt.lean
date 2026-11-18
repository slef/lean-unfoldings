module

public import Unfoldings.Geometry.PolygonalChain

/-! Literal polygonal chains are determined by their initial point and directed edge vectors. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] {n : ℕ}

/-- Retain all vertex positions, including the last endpoint and a chain with no edges. -/
theorem eq_of_start_edge_eq (P Q : PolygonalChain E n) (start : P.vertex 0 = Q.vertex 0)
    (edges : ∀ i, P.edge i = Q.edge i) : P = Q := by
  apply congrArg PolygonalChain.mk
  funext j
  induction j using Fin.induction with
  | zero => exact start
  | succ i previous =>
    have equal := edges i
    unfold edge at equal
    rw [previous] at equal
    exact sub_left_inj.mp equal

end Unfoldings.PolygonalChain
