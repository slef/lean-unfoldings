module

public import Unfoldings.FewestNets.MeshChartNormals
public import Unfoldings.Cap.Projection

/-! The physical certificate coordinates extend to an orthogonal spatial frame. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.MeshStar

variable {s : Space} (unit : ‖s‖ = 1)
  (genuine : bisectorTangent s (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)

/-- The chart coordinates occupy the first two coordinates, with the site pointing north. -/
def chartSpatialFrame : Space ≃ₗᵢ[ℝ] Space := (chartOrthonormalBasis unit genuine).repr

theorem chartSpatialFrame_horizontal (x : Space) :
    Cap.horizontal (chartSpatialFrame unit genuine x) = chartPoint s x := by
  ext i
  fin_cases i
  · change ((chartOrthonormalBasis unit genuine).repr x) 0 = inner ℝ x (chartFirst s)
    rw [OrthonormalBasis.repr_apply_apply, chartOrthonormalBasis_apply, real_inner_comm]
    rfl
  · change ((chartOrthonormalBasis unit genuine).repr x) 1 = inner ℝ x (chartSecond s)
    rw [OrthonormalBasis.repr_apply_apply, chartOrthonormalBasis_apply, real_inner_comm]
    rfl

theorem chartSpatialFrame_height (x : Space) :
    chartSpatialFrame unit genuine x 2 = inner ℝ x s := by
  change ((chartOrthonormalBasis unit genuine).repr x) 2 = _
  rw [OrthonormalBasis.repr_apply_apply, chartOrthonormalBasis_apply, real_inner_comm]
  rfl

include unit genuine in
theorem chartPoint_site_eq_zero : chartPoint s s = 0 := by
  obtain ⟨_, _, hu, hv, _⟩ := chartFrame_orthonormal unit genuine
  ext i
  fin_cases i
  · exact hu
  · exact hv

/-- The reference chart is genuine at every site strictly above the equator. -/
theorem tangent_firstAxis_ne_zero (upward : 0 < s 2) :
    bisectorTangent s (WithLp.toLp 2 ![1, 0, 0]) ≠ 0 := by
  intro same
  let x : Space := WithLp.toLp 2 ![1, 0, 0]
  have third := congrArg (fun z : Space => z 2) (sub_eq_zero.mp same)
  change 0 = inner ℝ s x * s 2 at third
  have dot : inner ℝ s x = 0 := (mul_eq_zero.mp third.symm).resolve_right upward.ne'
  change x - (inner ℝ s x) • s = 0 at same
  rw [dot, zero_smul, sub_zero] at same
  exact one_ne_zero (congrArg (fun z : Space => z 0) same)

end Unfoldings.FewestNets.MeshStar
