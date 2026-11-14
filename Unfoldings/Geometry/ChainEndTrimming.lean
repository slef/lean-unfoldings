module

public import Unfoldings.Geometry.ChainSplit

/-! Trim the first and last links while retaining every intermediate original corner. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E (n + 2))

/-- Two distinct terminal links permit independent endpoint fractions. -/
def trimEnds (a b : unitInterval) : PolygonalChain E (n + 2) where
  vertex j := if j.val = 0 then P.point 0 a else
    if j.val = n + 2 then P.point (Fin.last (n + 1)) b else P.vertex j

@[simp] theorem trimEnds_start (a b : unitInterval) :
    (P.trimEnds a b).vertex 0 = P.point 0 a := by simp [trimEnds]

@[simp] theorem trimEnds_last (a b : unitInterval) :
    (P.trimEnds a b).vertex (Fin.last (n + 2)) = P.point (Fin.last (n + 1)) b := by
  simp [trimEnds]

/-- Every intermediate original corner remains at its identical original point. -/
theorem trimEnds_vertex_internal (a b : unitInterval) (j : Fin (n + 3))
    (first : 0 < j.val) (last : j.val < n + 2) :
    (P.trimEnds a b).vertex j = P.vertex j := by
  simp only [trimEnds, ite_eq_right (by omega : ¬ j.val = 0),
    ite_eq_right (by omega : ¬ j.val = n + 2)]

theorem trimEnds_edge_first (a b : unitInterval) :
    (P.trimEnds a b).edge 0 = (1 - (a : ℝ)) • P.edge 0 := by
  rw [edge, Fin.castSucc_zero, P.trimEnds_start,
    P.trimEnds_vertex_internal a b _ (by simp) (by simp)]
  simp only [point, edge, AffineMap.lineMap_apply_module']
  module

theorem trimEnds_edge_last (a b : unitInterval) :
    (P.trimEnds a b).edge (Fin.last (n + 1)) = (b : ℝ) • P.edge (Fin.last (n + 1)) := by
  rw [edge, Fin.succ_last, P.trimEnds_last,
    P.trimEnds_vertex_internal a b _ (by simp) (by simp)]
  simp only [point, edge, AffineMap.lineMap_apply_module']
  module

theorem trimEnds_edge_internal (a b : unitInterval) (i : Fin (n + 2))
    (first : 0 < i.val) (last : i.val < n + 1) :
    (P.trimEnds a b).edge i = P.edge i := by
  rw [edge, P.trimEnds_vertex_internal a b i.succ
    (by change 0 < i.val + 1; omega) (by change i.val + 1 < n + 2; omega),
    P.trimEnds_vertex_internal a b i.castSucc first (by change i.val < n + 2; omega)]
  rfl

/-- The exact factor is positive for genuine trimming and allows contact at limiting fractions. -/
theorem trimEnds_edge (a b : unitInterval) (i : Fin (n + 2)) :
    (P.trimEnds a b).edge i =
      (if i.val = 0 then 1 - (a : ℝ) else if i.val = n + 1 then (b : ℝ) else 1) • P.edge i := by
  by_cases first : i.val = 0
  · have same : i = 0 := Fin.ext first
    rw [same, P.trimEnds_edge_first]
    simp
  · by_cases last : i.val = n + 1
    · have same : i = Fin.last (n + 1) := Fin.ext last
      rw [same, P.trimEnds_edge_last]
      simp
    · rw [P.trimEnds_edge_internal a b i (by omega) (by omega)]
      simp only [ite_eq_right first, ite_eq_right last, one_smul]

end Unfoldings.PolygonalChain
