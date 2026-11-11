module

public import Unfoldings.Geometry.AngleMonotone

/-! Append a final vertex while keeping whole-edge direction data explicit. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n)

def snoc (last : E) : PolygonalChain E (n + 1) where
  vertex := Fin.lastCases last P.vertex

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] theorem snoc_vertex_castSucc (last : E) (i : Fin (n + 1)) :
    (P.snoc last).vertex i.castSucc = P.vertex i := by
  simp only [snoc, Fin.lastCases_castSucc]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] theorem snoc_vertex_last (last : E) :
    (P.snoc last).vertex (Fin.last (n + 1)) = last := by
  simp only [snoc, Fin.lastCases_last]

omit [InnerProductSpace ℝ E] in
@[simp] theorem snoc_edge_castSucc (last : E) (i : Fin n) :
    (P.snoc last).edge i.castSucc = P.edge i := by
  change (P.snoc last).vertex i.succ.castSucc -
    (P.snoc last).vertex i.castSucc.castSucc = _
  rw [snoc_vertex_castSucc, snoc_vertex_castSucc]
  rfl

omit [InnerProductSpace ℝ E] in
@[simp] theorem snoc_edge_last (last : E) :
    (P.snoc last).edge (Fin.last n) = last - P.vertex (Fin.last n) := by
  change (P.snoc last).vertex (Fin.last (n + 1)) -
    (P.snoc last).vertex (Fin.last n).castSucc = _
  rw [snoc_vertex_last, snoc_vertex_castSucc]

/-- The final edge may lie on a wedge bank; no artificial strictness is needed. -/
theorem snoc_directions {u v last : E}
    (directions : ∀ i, InDirectionWedge u v (P.edge i))
    (final : InDirectionWedge u v (last - P.vertex (Fin.last n))) :
    ∀ i, InDirectionWedge u v ((P.snoc last).edge i) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [snoc_edge_last] using final
  · simpa only [snoc_edge_castSucc] using directions j

end Unfoldings.PolygonalChain
