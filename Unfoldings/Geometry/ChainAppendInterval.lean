module

public import Unfoldings.Geometry.ChainAppend
public import Unfoldings.Geometry.ChainInterval

/-! Appending a final vertex commutes with taking a terminal interval of the original chain. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n)

/-- Appending retains every original point of every original directed edge. -/
theorem snoc_point_castSucc (last : E) (i : Fin n) (t : unitInterval) :
    (P.snoc last).point i.castSucc t = P.point i t := by
  change AffineMap.lineMap ((P.snoc last).vertex i.castSucc.castSucc)
    ((P.snoc last).vertex i.succ.castSucc) (t : ℝ) = P.point i t
  rw [snoc_vertex_castSucc, snoc_vertex_castSucc]
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- A terminal subchain keeps its exact original vertices when the same endpoint is appended. -/
theorem interval_snoc (first length : ℕ) (at_end : first + length = n) (last : E) :
    (P.interval first length at_end.le).snoc last =
      (P.snoc last).interval first (length + 1) (by omega) := by
  apply congrArg PolygonalChain.mk
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · change ((P.interval first length at_end.le).snoc last).vertex (Fin.last (length + 1)) =
      (P.snoc last).vertex ⟨first + (length + 1), by omega⟩
    rw [snoc_vertex_last]
    have index : (⟨first + (length + 1), by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := by
      apply Fin.ext
      change first + (length + 1) = n + 1
      omega
    rw [index, snoc_vertex_last]
  · simp only [Fin.lastCases_castSucc]
    change P.vertex ⟨first + k.val, by omega⟩ =
      (P.snoc last).vertex (⟨first + k.val, by omega⟩ : Fin (n + 1)).castSucc
    exact (P.snoc_vertex_castSucc last _).symm

end Unfoldings.PolygonalChain
