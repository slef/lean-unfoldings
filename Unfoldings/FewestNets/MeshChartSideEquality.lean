module

public import Unfoldings.FewestNets.MeshChartNormals

/-! Exact equality on every named model side and both cyclic endpoints. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.MeshStar

open NormedSpace

theorem chart_bisector_eq_iff {s t N : Space} (unit : ‖s‖ = 1) (neighbor : ‖t‖ = 1)
    (genuine : bisectorTangent s (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)
    (height : 0 < inner ℝ s N) (side : bisectorTangent s t ≠ 0) :
    inner ℝ (chartPoint s (meshGnomonic s N)) (chartPoint s (normalize (bisectorTangent s t))) =
      ‖bisectorTangent s t‖ / (1 + inner ℝ s t) ↔ inner ℝ N t = inner ℝ N s := by
  let E := bisectorTangent s t
  let d := inner ℝ s t
  have Epos : 0 < ‖E‖ := norm_pos_iff.mpr side
  have square : ‖E‖ ^ 2 = 1 - d ^ 2 := by
    dsimp [E, bisectorTangent, d]
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, unit, neighbor, one_pow,
      mul_one, real_inner_smul_right, real_inner_comm s t]
    ring
  have d_pos : 0 < 1 + d := by
    have lower : -1 ≤ d := by
      have h := abs_real_inner_le_norm s t
      rw [unit, neighbor, one_mul] at h
      exact (abs_le.mp h).1
    have ne : d ≠ -1 := by
      intro bad
      rw [bad] at square
      norm_num at square
      exact side square
    linarith only [lt_of_le_of_ne lower (Ne.symm ne)]
  have off : ‖E‖ / (1 + d) = (1 - d) / ‖E‖ := by
    apply (div_eq_div_iff d_pos.ne' Epos.ne').mpr
    nlinarith only [square]
  have perp : inner ℝ s (normalize E) = 0 := by
    rw [NormedSpace.normalize, real_inner_smul_right, inner_bisectorTangent s t unit, mul_zero]
  have h := inner_meshGnomonic unit height.ne'
  change inner ℝ (chartPoint s (meshGnomonic s N)) (chartPoint s (normalize E)) =
    ‖E‖ / (1 + d) ↔ _
  rw [chartPoint_inner unit genuine perp, off, NormedSpace.normalize, real_inner_smul_right,
    ← div_eq_inv_mul, div_left_inj' Epos.ne']
  have inner_eq : inner ℝ (meshGnomonic s N) E =
      (inner ℝ s N)⁻¹ * inner ℝ N t - d := by
    have orthogonal : inner ℝ (meshGnomonic s N) s = 0 := (real_inner_comm s _).trans h
    rw [show E = t - d • s from rfl, inner_sub_right, real_inner_smul_right, orthogonal,
      mul_zero, sub_zero, meshGnomonic, inner_sub_left, real_inner_smul_left]
  rw [inner_eq, sub_left_inj, ← div_eq_inv_mul, div_eq_iff height.ne', one_mul,
    real_inner_comm s N]

theorem chart_bisector_lt_iff {s t N : Space} (unit : ‖s‖ = 1) (neighbor : ‖t‖ = 1)
    (genuine : bisectorTangent s (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)
    (height : 0 < inner ℝ s N) (side : bisectorTangent s t ≠ 0) :
    inner ℝ (chartPoint s (meshGnomonic s N)) (chartPoint s (normalize (bisectorTangent s t))) <
      ‖bisectorTangent s t‖ / (1 + inner ℝ s t) ↔ inner ℝ N t < inner ℝ N s := by
  simp only [lt_iff_le_and_ne, ne_eq, chart_bisector_le_iff unit neighbor genuine height side,
    chart_bisector_eq_iff unit neighbor genuine height side]

variable {n : ℕ} (M : MeshStar (n + 1))

/-- Corner k lies on the two genuine bisectors indexed by k and k+1. -/
theorem physicalVertex_on_side (unit : ‖M.direction‖ = 1)
    (genuine : bisectorTangent M.direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)
    {k i : Fin (n + 1)} (neighbor : ‖M.neighborDirection i‖ = 1)
    (side : bisectorTangent M.direction (M.neighborDirection i) ≠ 0)
    (outward : 0 < inner ℝ M.direction (M.dual k)) (incident : i = k ∨ i = k + 1) :
    inner ℝ (M.physicalVertex k) (M.physicalSideNormal i) = M.physicalSideOffset i := by
  apply (chart_bisector_eq_iff unit neighbor genuine outward side).mpr
  have ties := M.inner_dual_eq_neighbors k
  rw [real_inner_comm (M.neighborDirection i), real_inner_comm M.direction]
  rcases incident with rfl | rfl
  · exact ties.1.symm
  · exact ties.2.symm

/-- Both exact endpoints of the rescaled side lie on its certified support line. -/
theorem normalizedSide_on_support_line (unit : ‖M.direction‖ = 1)
    (genuine : bisectorTangent M.direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)
    (i : Fin (n + 1)) (neighbor : ‖M.neighborDirection i‖ = 1)
    (side : bisectorTangent M.direction (M.neighborDirection i) ≠ 0)
    (outward : ∀ k, 0 < inner ℝ M.direction (M.dual k))
    (r t : ℝ) :
    inner ℝ (AffineMap.lineMap (r⁻¹ • M.physicalVertex (i - 1)) (r⁻¹ • M.physicalVertex i) t)
      (M.physicalSideNormal i) = M.physicalSideOffset i / r := by
  have first := M.physicalVertex_on_side unit genuine neighbor side (outward (i - 1))
    (Or.inr (sub_add_cancel i 1).symm)
  have last := M.physicalVertex_on_side unit genuine neighbor side (outward i) (Or.inl rfl)
  rw [AffineMap.lineMap_apply_module']
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left, first, last]
  ring

end Unfoldings.FewestNets.MeshStar
