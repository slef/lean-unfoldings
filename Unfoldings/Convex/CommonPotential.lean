module

public import Unfoldings.Convex.SlopeEnvelope
public import Unfoldings.Geometry.AngleConeBound

/-! A single convex potential controls length and every incoming history at a merger. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope

variable (E : SlopeEnvelope)

theorem height_sub_le_norm {b : ℝ} (bounded : ∀ p ∈ E.slopes, ‖p‖ ≤ b) (x y : Plane) :
    E.height x - E.height y ≤ b * ‖x - y‖ := by
  obtain ⟨p, active⟩ := E.exists_active x
  exact (E.active_support active y).trans
    ((real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (bounded p active.1) (norm_nonneg _)))

/-- Any path with cumulative potential progress has a uniform length-to-chord bound. -/
theorem history_length_bound {b c length : ℝ} (positive : 0 < c)
    (bounded : ∀ p ∈ E.slopes, ‖p‖ ≤ b) {x y : Plane}
    (progress : c * length ≤ E.height x - E.height y) :
    length ≤ (b / c) * ‖x - y‖ := by
  have bound := progress.trans (E.height_sub_le_norm bounded x y)
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ positive).mpr (by nlinarith)

/-- Every active slope at the merger controls every incoming path, even when that path
was chosen using different slopes at its earlier vertices. -/
theorem history_cosine_bound {b c length : ℝ} (positive : 0 < b) (nonnegative : 0 ≤ c)
    (bounded : ∀ p ∈ E.slopes, ‖p‖ ≤ b) {x y p : Plane} (active : E.Active x p)
    (progress : c * length ≤ E.height x - E.height y) (chord : ‖x - y‖ ≤ length) :
    (c / b) * (‖p‖ * ‖x - y‖) ≤ inner ℝ p (x - y) := by
  calc
    _ ≤ (c / b) * (b * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (bounded p active.1) (norm_nonneg _))
        (div_nonneg nonnegative positive.le)
    _ = c * ‖x - y‖ := by field_simp
    _ ≤ c * length := mul_le_mul_of_nonneg_left chord nonnegative
    _ ≤ E.height x - E.height y := progress
    _ ≤ inner ℝ p (x - y) := E.active_support active y

theorem history_angle_bound {b c length : ℝ} (positive : 0 < b) (nonnegative : 0 ≤ c)
    (ratio : c ≤ b) (bounded : ∀ p ∈ E.slopes, ‖p‖ ≤ b) {x y p : Plane}
    (active : E.Active x p) (pne : p ≠ 0) (different : x ≠ y)
    (progress : c * length ≤ E.height x - E.height y) (chord : ‖x - y‖ ≤ length) :
    InnerProductGeometry.angle p (x - y) ≤ Real.arccos (c / b) := by
  apply (angle_le_iff_cos_mul_norm_le pne (sub_ne_zero.mpr different)
    (Real.arccos_nonneg _) (Real.arccos_le_pi _)).mpr
  rw [Real.cos_arccos (by linarith [div_nonneg nonnegative positive.le])
    ((div_le_one positive).mpr ratio)]
  exact E.history_cosine_bound positive nonnegative bounded active progress chord

/-- A local outgoing angle bound gives one quantitative radial margin for every incoming
history at this merger. No preferred predecessor or single-source choice occurs. -/
theorem history_radial_margin {b c length δ : ℝ} (positive : 0 < b) (nonnegative : 0 ≤ c)
    (ratio : c ≤ b) (bounded : ∀ p ∈ E.slopes, ‖p‖ ≤ b) {x y p edge : Plane}
    (active : E.Active x p) (pne : p ≠ 0) (different : x ≠ y) (edge_ne : edge ≠ 0)
    (progress : c * length ≤ E.height x - E.height y) (chord : ‖x - y‖ ≤ length)
    (outgoing : InnerProductGeometry.angle p edge ≤ δ) (delta : 0 ≤ δ)
    (small : Real.arccos (c / b) + δ ≤ Real.pi) :
    Real.cos (Real.arccos (c / b) + δ) * (‖x - y‖ * ‖edge‖) ≤
      inner ℝ (x - y) edge := by
  apply (angle_le_iff_cos_mul_norm_le (sub_ne_zero.mpr different) edge_ne
    (add_nonneg (Real.arccos_nonneg _) delta) small).mp
  have angle := E.history_angle_bound positive nonnegative ratio bounded active pne different
    progress chord
  have triangle := InnerProductGeometry.angle_le_angle_add_angle (x - y) p edge
  rw [InnerProductGeometry.angle_comm (x - y) p] at triangle
  linarith

end Unfoldings.SlopeEnvelope
