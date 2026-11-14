module

public import Unfoldings.Geometry.PolygonalLength

/-! Exact contiguous subchains, retaining their original vertices and edge vectors. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n)

/-- The first vertex and number of edges specify an actual contiguous subchain. -/
def interval (first length : ℕ) (fits : first + length ≤ n) : PolygonalChain E length where
  vertex j := P.vertex ⟨first + j.val, by omega⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] theorem interval_start (first length : ℕ) (fits : first + length ≤ n) :
    (P.interval first length fits).vertex 0 = P.vertex ⟨first, by omega⟩ := by
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] theorem interval_last (first length : ℕ) (fits : first + length ≤ n) :
    (P.interval first length fits).vertex (Fin.last length) =
      P.vertex ⟨first + length, by omega⟩ := rfl

omit [InnerProductSpace ℝ E] in
@[simp] theorem interval_edge (first length : ℕ) (fits : first + length ≤ n)
    (i : Fin length) :
    (P.interval first length fits).edge i = P.edge ⟨first + i.val, by omega⟩ := rfl

@[simp] theorem interval_point (first length : ℕ) (fits : first + length ≤ n)
    (i : Fin length) (t : unitInterval) :
    (P.interval first length fits).point i t = P.point ⟨first + i.val, by omega⟩ t := rfl

end Unfoldings.PolygonalChain
