module

public import Unfoldings.Roof.CurvatureBudget

/-!
# A curvature threshold quantified before the entire mesh

The numerical budget is a function of the normal-height bound alone. The final
threshold precedes even the face type and triangle complex in the theorem statement.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Filter Topology MeasureTheory
open scoped ENNReal

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- A deliberately conservative, explicit normal-height bound on total intrinsic curvature. -/
theorem totalCurvature_le_normal_budget {c : ℝ} (lower : (3 : ℝ) / 4 ≤ c)
    (height : ∀ f, c ≤ K.normal f 2) :
    C.totalInteriorAngularDefect Set.univ ≤
      81 * (Real.sqrt (1 - c ^ 2) / c) ^ 2 * Real.pi := by
  have positive : 0 < c := lt_of_lt_of_le (by norm_num) lower
  have radius : 0 ≤ Real.sqrt (1 - c ^ 2) / c := div_nonneg (Real.sqrt_nonneg _) positive.le
  have plane : (81 : ℝ≥0∞) * (∑ v : C.Vertex Set.univ, volume (K.normalPolygon v)) ≤
      81 * (ENNReal.ofReal (Real.sqrt (1 - c ^ 2) / c) ^ 2 * ENNReal.ofReal Real.pi) := by
    gcongr
    exact K.normalPolygon_area_budget positive height
  have bound := K.ofReal_totalCurvature_le_solid_normal_area.trans
    ((K.sum_solidNormalPolygon_area_le (fun f => lower.trans (height f))).trans plane)
  have converted : (81 : ℝ≥0∞) *
      (ENNReal.ofReal (Real.sqrt (1 - c ^ 2) / c) ^ 2 * ENNReal.ofReal Real.pi) =
      ENNReal.ofReal (81 * (Real.sqrt (1 - c ^ 2) / c) ^ 2 * Real.pi) := by
    rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) (sq_nonneg _)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 81), ENNReal.ofReal_pow radius]
    norm_num
    ring
  rw [converted] at bound
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp bound

/-- The choice is purely numerical and has no cap, face set, or complex parameter. -/
theorem exists_positive_tilt_curvature_budget {ε : ℝ} (positive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (3 : ℝ) / 4 ≤ Real.cos φ ∧
      81 * (Real.sqrt (1 - Real.cos φ ^ 2) / Real.cos φ) ^ 2 * Real.pi < ε := by
  let area : ℝ → ℝ := fun φ =>
    81 * (Real.sqrt (1 - Real.cos φ ^ 2) / Real.cos φ) ^ 2 * Real.pi
  have continuous : ContinuousAt area 0 := by
    dsimp only [area]
    fun_prop (disch := norm_num)
  have at_zero : area 0 = 0 := by simp [area]
  have near_area : ∀ᶠ φ in 𝓝 (0 : ℝ), area φ < ε :=
    continuous.eventually (gt_mem_nhds (by rw [at_zero]; exact positive))
  have near_cos : ∀ᶠ φ in 𝓝 (0 : ℝ), (3 : ℝ) / 4 < Real.cos φ :=
    Real.continuous_cos.continuousAt.eventually (lt_mem_nhds (by norm_num))
  obtain ⟨δ, δpos, bound⟩ := Metric.eventually_nhds_iff.mp (near_area.and near_cos)
  let φ : ℝ := min (δ / 2) (Real.pi / 4)
  have φpos : 0 < φ := lt_min (by positivity) (by positivity)
  have φδ : φ < δ := (min_le_left _ _).trans_lt (by linarith)
  have good := bound (show dist φ 0 < δ by
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos φpos] using φδ)
  exact ⟨φ, ⟨φpos, (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])⟩,
    good.2.le, good.1⟩

/-- The same positive threshold works for every input mesh in the given universes. -/
theorem exists_uniform_tilt_totalCurvature_lt {ε : ℝ} (positive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face' : Type u} [Fintype Face'] {C' : TriangleComplex.{u, v} Face'}
        (K : ConvexRoof C'), K.TiltBound φ → C'.totalInteriorAngularDefect Set.univ < ε := by
  obtain ⟨φ, bounds, lower, budget⟩ := exists_positive_tilt_curvature_budget positive
  exact ⟨φ, bounds, fun K tilt => (K.totalCurvature_le_normal_budget lower tilt).trans_lt budget⟩

end Unfoldings.ConvexRoof
