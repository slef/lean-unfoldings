module

public import Unfoldings.Geometry.GenericRadialSource
public import Unfoldings.Geometry.ChainEndTrimPaths

/-! Positive actual radial progress remains strict after trimming both endpoint links. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n)

/-- Positive radial progress at an edge's initial point is positive along its whole length. -/
theorem strictRadialSource_point_inner {source : Plane} (strict : source ∈ P.strictRadialSources)
    (i : Fin n) (nonzero : P.edge i ≠ 0) (t : unitInterval) :
    0 < inner ℝ (P.point i t - source) (P.edge i) := by
  have vector : P.point i t - source = (P.vertex i.castSucc - source) + (t : ℝ) • P.edge i := by
    simp only [point, edge, AffineMap.lineMap_apply_module']
    module
  rw [vector, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  exact add_pos_of_pos_of_nonneg (strict i nonzero) (mul_nonneg t.property.1 (sq_nonneg _))

/-- Every nonzero trimmed link still has strictly positive progress from the same source. -/
theorem strictRadialSource_trimEnds (P : PolygonalChain Plane (n + 2)) {source : Plane}
    (strict : source ∈ P.strictRadialSources) (a b : unitInterval)
    (first : (a : ℝ) < 1) (last : 0 < (b : ℝ)) :
    source ∈ (P.trimEnds a b).strictRadialSources := by
  intro i nonzero
  have original : P.edge i ≠ 0 := by
    intro zero
    apply nonzero
    rw [P.trimEnds_edge, zero, smul_zero]
  have position : (P.trimEnds a b).vertex i.castSucc = P.point i (trimEndsParameter a b i 0) :=
    ((P.trimEnds a b).point_zero i).symm.trans (P.trimEnds_point a b i 0)
  have positive : 0 < (if i.val = 0 then 1 - (a : ℝ) else
      if i.val = n + 1 then (b : ℝ) else 1) := by
    split_ifs <;> linarith
  rw [position, P.trimEnds_edge, real_inner_smul_right]
  exact mul_pos positive (P.strictRadialSource_point_inner strict i original _)

end Unfoldings.PolygonalChain
