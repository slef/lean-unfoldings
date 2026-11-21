module

public import Unfoldings.Geometry.StrictRadialTrimming
public import Unfoldings.Geometry.PolygonalVertexRays

/-! Trimming a radial block that starts exactly at its comparison source. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane (n + 2))

/-- After trimming into the first link, a source-starting block has positive
initial radius and strict radial progress, preserving all its internal turns. -/
theorem strictRadialSource_trimEnds_start_at_source {source : Plane} (start : P.vertex 0 = source)
    (radial : P.RadialFrom source 0) (nonzero : ∀ i, P.edge i ≠ 0) {gamma : ℝ}
    (positive : 0 < gamma)
    (margin : ∀ i, gamma * (‖P.vertex i.castSucc - source‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - source) (P.edge i))
    (a b : unitInterval) (ap : 0 < (a : ℝ)) (a_small : (a : ℝ) < 1) (bp : 0 < (b : ℝ)) :
    source ∈ (P.trimEnds a b).strictRadialSources ∧
      0 < dist source ((P.trimEnds a b).vertex 0) := by
  have vector (i : Fin (n + 2)) (t : unitInterval) :
      P.point i t - source = (P.vertex i.castSucc - source) + (t : ℝ) • P.edge i := by
    simp only [point, edge, AffineMap.lineMap_apply_module']
    module
  have at_start : P.point 0 a - source = (a : ℝ) • P.edge 0 := by
    rw [vector, Fin.castSucc_zero, start, sub_self, zero_add]
  have start_pos : 0 < dist source ((P.trimEnds a b).vertex 0) := by
    rw [P.trimEnds_start, dist_eq_norm', at_start, norm_smul, Real.norm_eq_abs, abs_of_pos ap]
    exact mul_pos ap (norm_pos_iff.mpr (nonzero 0))
  refine ⟨?_, start_pos⟩
  intro i _
  have ordered := P.vertex_radius_strictMono_of_radial source radial nonzero
  have pos (t : unitInterval) (it : i.val ≠ 0 ∨ 0 < (t : ℝ)) :
      0 < inner ℝ (P.point i t - source) (P.edge i) := by
    rw [vector, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have nonneg := (mul_nonneg positive.le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans
      (margin i)
    rcases it with past | displaced
    · have ix : (0 : Fin (n + 3)) < i.castSucc := by
        change 0 < i.val
        omega
      have radius : dist source (P.vertex 0) < dist source (P.vertex i.castSucc) := ordered ix
      rw [start, dist_self, dist_eq_norm'] at radius
      exact add_pos_of_pos_of_nonneg
        ((mul_pos positive (mul_pos radius (norm_pos_iff.mpr (nonzero i)))).trans_le (margin i))
        (mul_nonneg t.property.1 (sq_nonneg _))
    · exact add_pos_of_nonneg_of_pos nonneg
        (mul_pos displaced (sq_pos_of_ne_zero ((norm_ne_zero_iff).mpr (nonzero i))))
  have position : (P.trimEnds a b).vertex i.castSucc =
      P.point i (trimEndsParameter a b i 0) :=
    ((P.trimEnds a b).point_zero i).symm.trans (P.trimEnds_point a b i 0)
  have scale : 0 < (if i.val = 0 then 1 - (a : ℝ) else
      if i.val = n + 1 then (b : ℝ) else 1) := by
    split_ifs <;> linarith
  have parameter : i.val ≠ 0 ∨ 0 < (trimEndsParameter a b i 0 : ℝ) := by
    by_cases hi : i.val = 0
    · right
      simpa [trimEndsParameter, hi] using ap
    · exact Or.inl hi
  rw [position, P.trimEnds_edge, real_inner_smul_right]
  exact mul_pos scale (pos _ parameter)

end Unfoldings.PolygonalChain
