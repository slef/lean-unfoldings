module

public import Unfoldings.Geometry.AngleMonotone
public import Unfoldings.Geometry.RadialChainPoints
public import Unfoldings.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-! Examples distinguish whole-edge radial monotonicity from endpoint-only checks. -/

@[expose] public section

namespace Unfoldings.Examples

def endpointDistanceTrap : PolygonalChain ℝ 2 where
  vertex := ![0, 1, -2]

theorem endpointDistanceTrap_vertices_monotone :
    Monotone (fun i => dist (endpointDistanceTrap.vertex 0) (endpointDistanceTrap.vertex i)) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  fin_cases i <;> norm_num [endpointDistanceTrap, Real.dist_eq]

theorem endpointDistanceTrap_not_radial : ¬ endpointDistanceTrap.RadiallyMonotone := by
  intro radial
  have outward := (endpointDistanceTrap.radiallyMonotone_iff_outward.mp radial) 0 1 (by decide)
  norm_num [endpointDistanceTrap, PolygonalChain.edge, Real.inner_apply] at outward

def staircase : PolygonalChain Plane 2 where
  vertex := ![WithLp.toLp 2 ![0, 0], WithLp.toLp 2 ![1, 0], WithLp.toLp 2 ![1, 1]]

theorem staircase_edges_nonnegative : staircase.PairwiseNonnegativeEdges := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [PolygonalChain.edge, staircase, PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]

theorem staircase_globally_radial : staircase.GloballyRadiallyMonotone :=
  PolygonalChain.RadiallyMonotone.globallyRadiallyMonotone staircase
    (PolygonalChain.PairwiseNonnegativeEdges.radiallyMonotone staircase staircase_edges_nonnegative)

end Unfoldings.Examples
