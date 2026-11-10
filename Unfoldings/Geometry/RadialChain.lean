module

public import Unfoldings.Geometry.ChainOrder

/-! Whole-chain radial comparisons and uniqueness of points on a concentric sphere. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem lineMap_eq_of_dist_eq (a b c : E)
    (radial : Monotone (fun t : unitInterval => dist a (AffineMap.lineMap b c (t : ℝ))))
    (t s : unitInterval) (equal : dist a (AffineMap.lineMap b c (t : ℝ)) =
      dist a (AffineMap.lineMap b c (s : ℝ))) :
    AffineMap.lineMap b c (t : ℝ) = AffineMap.lineMap b c (s : ℝ) := by
  by_cases same : b = c
  · subst c
    simp only [AffineMap.lineMap_same, AffineMap.const_apply]
  · have outward := (monotone_dist_lineMap_iff a b c).mp radial
    have strict : StrictMono (fun t : unitInterval => dist a (AffineMap.lineMap b c (t : ℝ))) :=
      fun t s ordered => dist_lineMap_lt_of_inner_nonneg a b c outward same t.property.1 ordered
    exact congrArg (fun u : unitInterval => AffineMap.lineMap b c (u : ℝ)) (strict.injective equal)

namespace PolygonalChain

variable {n : ℕ} (P : PolygonalChain E n)

/-- Distance from a specified point is monotone on every edge after the named vertex. -/
def RadialFrom (a : E) (j : Fin (n + 1)) : Prop :=
  ∀ i : Fin n, j.val ≤ i.val → Monotone (fun t : unitInterval => dist a (P.point i t))

theorem RadialFrom.dist_vertices_le {a : E} {j : Fin (n + 1)} (radial : P.RadialFrom a j)
    (u v : Fin (n + 1)) (earlier : j ≤ u) (ordered : u ≤ v) :
    dist a (P.vertex u) ≤ dist a (P.vertex v) := by
  have monotone : Monotone (fun k : Fin (n + 1) => dist a (P.vertex (max j k))) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro k
    by_cases previous : j ≤ k.castSucc
    · rw [max_eq_right previous, max_eq_right (previous.trans (Fin.castSucc_le_succ k))]
      have bound := radial k previous (show (0 : unitInterval) ≤ 1 from zero_le_one)
      simpa only [point_zero, point_one] using bound
    · have before : k.succ ≤ j := by
        have small := lt_of_not_ge previous
        change k.val < j.val at small
        change k.val + 1 ≤ j.val
        omega
      rw [max_eq_left (le_of_not_ge previous), max_eq_left before]
  simpa only [max_eq_right earlier, max_eq_right (earlier.trans ordered)] using monotone ordered

theorem RadialFrom.dist_point_le {a : E} {j : Fin (n + 1)} (radial : P.RadialFrom a j)
    (i k : Fin n) (t s : unitInterval) (earlier : j.val ≤ i.val) (ordered : Before i t k s) :
    dist a (P.point i t) ≤ dist a (P.point k s) := by
  rcases ordered with different | ⟨rfl, parameters⟩
  · have previous : j.val ≤ k.val := earlier.trans (le_of_lt different)
    have first := radial i earlier (show t ≤ (1 : unitInterval) from t.property.2)
    have last := radial k previous (show (0 : unitInterval) ≤ s from s.property.1)
    have middle := RadialFrom.dist_vertices_le P radial i.succ k.castSucc
      (by change j.val ≤ i.val + 1; omega) (by change i.val + 1 ≤ k.val; omega)
    simp only [point_one, point_zero] at first last
    exact first.trans (middle.trans last)
  · exact radial i earlier parameters

/-- A constant radial distance across several edges forces all those edges to be constant. -/
theorem RadialFrom.vertex_eq_of_dist_eq {a : E} {j : Fin (n + 1)} (radial : P.RadialFrom a j)
    (u v : Fin (n + 1)) (earlier : j ≤ u) (ordered : u ≤ v)
    (equal : dist a (P.vertex u) = dist a (P.vertex v)) : P.vertex u = P.vertex v := by
  induction v using Fin.induction generalizing u with
  | zero =>
    have same : u = 0 := by
      apply Fin.ext
      change u.val ≤ 0 at ordered
      change u.val = 0
      omega
    subst u
    rfl
  | succ v ih =>
    by_cases previous : u ≤ v.castSucc
    · have start : j ≤ v.castSucc := earlier.trans previous
      have lower := RadialFrom.dist_vertices_le P radial u v.castSucc earlier previous
      have upper := RadialFrom.dist_vertices_le P radial v.castSucc v.succ start
        (Fin.castSucc_le_succ v)
      have middle : dist a (P.vertex u) = dist a (P.vertex v.castSucc) := by linarith
      have endpoints : dist a (P.vertex v.castSucc) = dist a (P.vertex v.succ) := by linarith
      have same := lineMap_eq_of_dist_eq a (P.vertex v.castSucc) (P.vertex v.succ)
        (radial v start) 0 1 (by simpa only [Set.Icc.coe_zero, Set.Icc.coe_one,
          AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using endpoints)
      have edge_equal : P.vertex v.castSucc = P.vertex v.succ := by
        simpa only [Set.Icc.coe_zero, Set.Icc.coe_one,
          AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using same
      exact (ih u earlier previous middle).trans edge_equal
    · have same : u = v.succ := by
        apply Fin.ext
        have after := lt_of_not_ge previous
        change v.val < u.val at after
        change u.val ≤ v.val + 1 at ordered
        change u.val = v.val + 1
        omega
      exact congrArg P.vertex same

/-- Each concentric sphere contains at most one actual point of the future chain. -/
theorem RadialFrom.point_eq_of_dist_eq {a : E} {j : Fin (n + 1)} (radial : P.RadialFrom a j)
    (i k : Fin n) (t s : unitInterval) (earlier : j.val ≤ i.val) (ordered : Before i t k s)
    (equal : dist a (P.point i t) = dist a (P.point k s)) : P.point i t = P.point k s := by
  rcases ordered with different | ⟨rfl, parameters⟩
  · have previous : j.val ≤ k.val := earlier.trans (le_of_lt different)
    have first := radial i earlier (show t ≤ (1 : unitInterval) from t.property.2)
    have last := radial k previous (show (0 : unitInterval) ≤ s from s.property.1)
    have middle := RadialFrom.dist_vertices_le P radial i.succ k.castSucc
      (by change j.val ≤ i.val + 1; omega) (by change i.val + 1 ≤ k.val; omega)
    simp only [point_zero, point_one] at first last
    have first_equal : dist a (P.point i t) = dist a (P.vertex i.succ) := by linarith
    have last_equal : dist a (P.point k 0) = dist a (P.point k s) := by
      rw [point_zero]
      linarith
    have mid_equal : dist a (P.vertex i.succ) = dist a (P.vertex k.castSucc) := by linarith
    have first_point := lineMap_eq_of_dist_eq a (P.vertex i.castSucc) (P.vertex i.succ)
      (radial i earlier) t 1 (by
        simpa only [Set.Icc.coe_one, AffineMap.lineMap_apply_one, point] using first_equal)
    have last_point := lineMap_eq_of_dist_eq a (P.vertex k.castSucc) (P.vertex k.succ)
      (radial k previous) 0 s last_equal
    have vertex_equal := RadialFrom.vertex_eq_of_dist_eq P radial i.succ k.castSucc
      (by change j.val ≤ i.val + 1; omega) (by change i.val + 1 ≤ k.val; omega) mid_equal
    have first_point' : P.point i t = P.vertex i.succ := by
      simpa only [Set.Icc.coe_one, AffineMap.lineMap_apply_one, point] using first_point
    have last_point' : P.vertex k.castSucc = P.point k s := by
      simpa only [Set.Icc.coe_zero, AffineMap.lineMap_apply_zero, point] using last_point
    exact first_point'.trans (vertex_equal.trans last_point')
  · exact lineMap_eq_of_dist_eq _ _ _ (radial i earlier) t s equal

end PolygonalChain
end Unfoldings
