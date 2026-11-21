module

public import Unfoldings.FewestNets.MeshChartSupport
public import Unfoldings.FewestNets.CheckedMeshChart

/-! Exact unit side normals and affine chart rescaling. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.MeshStar

open NormedSpace

/-- The two tangent-coordinate functionals form a linear map. -/
def chartPointLinear (s : Space) : Space →ₗ[ℝ] Plane where
  toFun := chartPoint s
  map_add' x y := by
    ext j
    fin_cases j <;> simp [chartPoint, inner_add_left]
  map_smul' c x := by
    ext j
    fin_cases j <;> simp [chartPoint, real_inner_smul_left]

theorem chartPoint_norm_of_tangent {s x : Space} (unit : ‖s‖ = 1)
    (genuine : bisectorTangent s (WithLp.toLp 2 ![1, 0, 0]) ≠ 0) (hx : inner ℝ s x = 0) :
    ‖chartPoint s x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  exact chartPoint_inner unit genuine hx

/-- Lift tangent coordinates to the plane with height one over the site. -/
def chartLift (s : Space) (p : Plane) : Space :=
  s + p 0 • chartFirst s + p 1 • chartSecond s

theorem inner_chartLift {s : Space} (unit : ‖s‖ = 1)
    (genuine : bisectorTangent s (WithLp.toLp 2 ![1, 0, 0]) ≠ 0) (p : Plane) :
    inner ℝ s (chartLift s p) = 1 := by
  obtain ⟨_, _, su, sv, _⟩ := chartFrame_orthonormal unit genuine
  simp [chartLift, inner_add_right, real_inner_smul_right, unit, su, sv]

theorem chartPoint_meshGnomonic_chartLift {s : Space} (unit : ‖s‖ = 1)
    (genuine : bisectorTangent s (WithLp.toLp 2 ![1, 0, 0]) ≠ 0) (p : Plane) :
    chartPoint s (meshGnomonic s (chartLift s p)) = p := by
  obtain ⟨u, v, _, _, uv⟩ := chartFrame_orthonormal unit genuine
  have vu : inner ℝ (chartSecond s) (chartFirst s) = 0 := (real_inner_comm _ _).trans uv
  rw [meshGnomonic, inner_chartLift unit genuine, inv_one, one_smul]
  have eq : chartLift s p - s = p 0 • chartFirst s + p 1 • chartSecond s := by
    unfold chartLift
    abel
  rw [eq]
  ext j
  fin_cases j <;>
    simp [chartPoint, inner_add_left, real_inner_smul_left, uv, vu, u, v]

theorem physicalSideNormal_unit {n : ℕ} (star : MeshStar (n + 1)) (i : Fin (n + 1))
    (unit : ‖star.direction‖ = 1)
    (genuine : bisectorTangent star.direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)
    (side : bisectorTangent star.direction (star.neighborDirection i) ≠ 0) :
    ‖star.physicalSideNormal i‖ = 1 := by
  let b := bisectorTangent star.direction (star.neighborDirection i)
  have hb : inner ℝ star.direction (normalize b) = 0 := by
    rw [NormedSpace.normalize, real_inner_smul_right,
      inner_bisectorTangent star.direction (star.neighborDirection i) unit, mul_zero]
  change ‖chartPoint star.direction (normalize b)‖ = 1
  rw [chartPoint_norm_of_tangent unit genuine hb, norm_normalize side]

/-- The exact support inequality is preserved by the certificate's positive chart rescaling. -/
theorem derivative_chart_bisector_le_iff {n : ℕ} (star : MeshStar (n + 1)) (q : ℕ)
    (i : Fin (n + 1)) {N : Space} (unit : ‖star.direction‖ = 1)
    (neighbor : ‖star.neighborDirection i‖ = 1)
    (genuine : bisectorTangent star.direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)
    (height : 0 < inner ℝ star.direction N)
    (side : bisectorTangent star.direction (star.neighborDirection i) ≠ 0)
    (positive : 0 < star.derivativeRadius q) :
    inner ℝ ((star.derivativeRadius q)⁻¹ • chartPoint star.direction
      (meshGnomonic star.direction N)) (star.physicalSideNormal i) ≤
      star.derivativeNormalizedSideOffset q i ↔
    inner ℝ N (star.neighborDirection i) ≤ inner ℝ N star.direction := by
  rw [real_inner_smul_left, ← div_eq_inv_mul, derivativeNormalizedSideOffset,
    div_le_div_iff_of_pos_right positive]
  exact chart_bisector_le_iff unit neighbor genuine height side

end Unfoldings.FewestNets.MeshStar
