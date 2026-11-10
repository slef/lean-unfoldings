module

public import Unfoldings.Geometry.RadialChain

/-! Radial monotonicity from earlier points inside edges, not only from chain vertices. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n)

/-- The actual ordered-point condition on the whole polygonal chain. -/
def GloballyRadiallyMonotone : Prop :=
  ∀ (j i k : Fin n) (u t s : unitInterval), Before j u i t → Before i t k s →
    dist (P.point j u) (P.point i t) ≤ dist (P.point j u) (P.point k s)

theorem Outward.inner_point_nonneg (outward : P.Outward) (j i : Fin n)
    (earlier : j < i) (u : unitInterval) :
    0 ≤ inner ℝ (P.vertex i.castSucc - P.point j u) (P.edge i) := by
  have first := outward j.castSucc i (le_of_lt earlier)
  have last := outward j.succ i (by change j.val + 1 ≤ i.val; omega)
  have expression : inner ℝ (P.vertex i.castSucc - P.point j u) (P.edge i) =
      (1 - (u : ℝ)) * inner ℝ (P.vertex i.castSucc - P.vertex j.castSucc) (P.edge i) +
      (u : ℝ) * inner ℝ (P.vertex i.castSucc - P.vertex j.succ) (P.edge i) := by
    simp only [point, AffineMap.lineMap_apply_module', inner_sub_left,
      inner_add_left, real_inner_smul_left]
    ring
  rw [expression]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr u.property.2) first) (mul_nonneg u.property.1 last)

theorem Outward.radialFrom_point_after (outward : P.Outward) (j : Fin n) (u : unitInterval) :
    P.RadialFrom (P.point j u) j.succ := by
  intro i earlier
  apply (monotone_dist_lineMap_iff _ _ _).mpr
  exact Outward.inner_point_nonneg P outward j i (by change j.val + 1 ≤ i.val at earlier; omega) u

theorem dist_point_same_edge (j : Fin n) (u t : unitInterval) (ordered : u ≤ t) :
    dist (P.point j u) (P.point j t) = ((t : ℝ) - (u : ℝ)) *
      dist (P.vertex j.castSucc) (P.vertex j.succ) := by
  rw [point, point, dist_lineMap_lineMap]
  have ordered' : (u : ℝ) ≤ (t : ℝ) := ordered
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ordered')]
  ring

/-- Outward tests at vertices control all ordered triples of actual chain points. -/
theorem Outward.globallyRadiallyMonotone (outward : P.Outward) : P.GloballyRadiallyMonotone := by
  intro j i k u t s first last
  rcases first with earlier | ⟨rfl, start_parameter⟩
  · exact RadialFrom.dist_point_le P (Outward.radialFrom_point_after P outward j u)
      i k t s (by change j.val + 1 ≤ i.val; omega) last
  · rcases last with later | ⟨rfl, parameters⟩
    · have radial := Outward.radialFrom_point_after P outward j u
      have first_bound : dist (P.point j u) (P.point j t) ≤
          dist (P.point j u) (P.point j 1) := by
        rw [dist_point_same_edge P j u t start_parameter,
          dist_point_same_edge P j u 1 u.property.2]
        exact mul_le_mul_of_nonneg_right (sub_le_sub_right t.property.2 _) dist_nonneg
      have middle := RadialFrom.dist_vertices_le P radial j.succ k.castSucc le_rfl
        (by change j.val + 1 ≤ k.val; omega)
      have last_bound := radial k (by change j.val + 1 ≤ k.val; omega)
        (show (0 : unitInterval) ≤ s from s.property.1)
      simp only [point_zero, point_one] at first_bound last_bound
      exact first_bound.trans (middle.trans last_bound)
    · rw [dist_point_same_edge P j u t start_parameter,
        dist_point_same_edge P j u s (start_parameter.trans parameters)]
      exact mul_le_mul_of_nonneg_right
        (sub_le_sub_right (show (t : ℝ) ≤ (s : ℝ) from parameters) _) dist_nonneg

theorem RadiallyMonotone.globallyRadiallyMonotone (radial : P.RadiallyMonotone) :
    P.GloballyRadiallyMonotone :=
  Outward.globallyRadiallyMonotone P (P.radiallyMonotone_iff_outward.mp radial)

end Unfoldings.PolygonalChain
