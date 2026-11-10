module

public import Unfoldings.Metric.OpenChart
public import Unfoldings.Basic
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Affine.Isometry

/-! A rigid motion is determined by its expression on a neighborhood in an open metric chart. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {X : Type*} [MetricSpace X] {D : Set X} {U : Set Plane}

theorem rigid_eq_of_agrees_in_chart (chart : D ≃ᵢ U) (open_D : IsOpen D) (open_U : IsOpen U)
    (x : X) (member : x ∈ D) (A B : Plane ≃ᵃⁱ[ℝ] Plane) {r : ℝ} (positive : 0 < r)
    (agrees : ∀ y : D, dist y.val x < r → A (chart y).val = B (chart y).val) : A = B := by
  obtain ⟨a, apos, inside, cover⟩ := exists_open_chart_ball_radius chart open_D open_U ⟨x, member⟩
  let radius := min a r
  have rpos : 0 < radius := lt_min apos positive
  have inside' : Metric.ball x radius ⊆ D :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans inside
  have cover' : Metric.ball (chart ⟨x, member⟩).val radius ⊆ U :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans cover
  let localChart := restrictChartBall chart ⟨x, member⟩ inside' cover'
  have equal : A.toAffineMap = B.toAffineMap := by
    apply AffineMap.ext_on (Metric.isOpen_ball.affineSpan_eq_top
      ⟨(chart ⟨x, member⟩).val, Metric.mem_ball_self rpos⟩)
    intro z hz
    let y := localChart.symm ⟨z, hz⟩
    have coordinates := congrArg Subtype.val (localChart.apply_symm_apply ⟨z, hz⟩)
    change (chart ⟨y.val, inside' y.property⟩).val = z at coordinates
    change A z = B z
    rw [← coordinates]
    exact agrees ⟨y.val, inside' y.property⟩
      ((Metric.mem_ball.mp y.property).trans_le (min_le_right a r))
  apply AffineIsometryEquiv.ext
  intro z
  exact congrArg (fun h : Plane →ᵃ[ℝ] Plane => h z) equal

end Unfoldings
