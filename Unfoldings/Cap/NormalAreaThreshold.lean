module

public import Unfoldings.Cap.NormalArea

/-!
# Uniform smallness of the complete planar normal image

Any requested positive area budget admits a positive tilt threshold, chosen
before the cap. This is a geometric area statement independent of vertex count;
identification of intrinsic curvature with spherical normal area remains open.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open Filter Topology MeasureTheory

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}

/-- The total normal-polygon area is arbitrarily small for sufficiently small positive tilt. -/
theorem exists_tilt_normal_area_lt {ε : ℝ} (positive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ K : ConvexCap C, K.TiltBound φ →
      (∑ v : C.Vertex Set.univ, volume (K.normalPolygon v)) < ENNReal.ofReal ε := by
  let area : ℝ → ℝ := fun φ => (Real.sqrt (1 - Real.cos φ ^ 2) / Real.cos φ) ^ 2 * Real.pi
  have continuous : ContinuousAt area 0 := by
    dsimp only [area]
    fun_prop (disch := norm_num)
  have at_zero : area 0 = 0 := by simp [area]
  have near_area : ∀ᶠ φ in 𝓝 (0 : ℝ), area φ < ε :=
    continuous.eventually (gt_mem_nhds (by rw [at_zero]; exact positive))
  have near_cos : ∀ᶠ φ in 𝓝 (0 : ℝ), 0 < Real.cos φ :=
    Real.continuous_cos.continuousAt.eventually (lt_mem_nhds (by norm_num))
  obtain ⟨δ, δpos, bound⟩ := Metric.eventually_nhds_iff.mp (near_area.and near_cos)
  let φ : ℝ := min (δ / 2) (Real.pi / 4)
  have φpos : 0 < φ := lt_min (by positivity) (by positivity)
  have φδ : φ < δ := (min_le_left _ _).trans_lt (by linarith)
  have good := bound (show dist φ 0 < δ by
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos φpos] using φδ)
  refine ⟨φ, ⟨φpos, (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])⟩, ?_⟩
  intro K tilt
  have estimate := K.normalPolygon_area_budget good.2 tilt
  have radius_nonnegative : 0 ≤ Real.sqrt (1 - Real.cos φ ^ 2) / Real.cos φ :=
    div_nonneg (Real.sqrt_nonneg _) good.2.le
  have converted : ENNReal.ofReal (Real.sqrt (1 - Real.cos φ ^ 2) / Real.cos φ) ^ 2 *
      ENNReal.ofReal Real.pi = ENNReal.ofReal (area φ) := by
    rw [← ENNReal.ofReal_pow radius_nonnegative, ← ENNReal.ofReal_mul (sq_nonneg _)]
  exact (estimate.trans_eq converted).trans_lt ((ENNReal.ofReal_lt_ofReal_iff positive).mpr good.1)

end Unfoldings.ConvexCap
