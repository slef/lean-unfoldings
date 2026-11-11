module

public import Unfoldings.Cap.StrictGeometricTailGraphs
public import Unfoldings.Cap.GeometricSectorBankPoints

/-! Source-centered sector strips have a positive coordinate margin depending only on the sector. -/

@[expose] public section

namespace Unfoldings

namespace AcuteWedgeFrame

variable {u v : Plane} (B : AcuteWedgeFrame u v)

theorem exists_enclosingStrip_coordinate_margin :
    ∃ μ > 0, ∀ z ∈ B.enclosingStrip.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im := by
  let S := B.enclosingStrip
  have strict := B.enclosingStrip_strictCoordinatesOn (Set.Icc (0 : ℝ) 1)
  have source := B.enclosingStrip_source
  have lower : 0 < S.lower.coordinate 1 := by
    have bound := strict.1.1 (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
      (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩) zero_lt_one
    rwa [source.1] at bound
  have upper : 0 < 1 - S.upper.coordinate 1 := by
    have bound := strict.2.2 (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
      (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩) zero_lt_one
    change 0 - B.enclosingStrip.upper.coordinate 0 <
      1 - B.enclosingStrip.upper.coordinate 1 at bound
    rwa [source.2, sub_self] at bound
  let μ := min (S.lower.coordinate 1) (1 - S.upper.coordinate 1)
  refine ⟨μ, lt_min lower upper, fun z member forward => ?_⟩
  have homogeneous := B.enclosingStrip_coordinate_homogeneous forward
  constructor
  · exact ((mul_le_mul_of_nonneg_right (min_le_left _ _) forward).trans_eq
      homogeneous.1.symm).trans member.1
  · have bound := mul_le_mul_of_nonneg_right (min_le_right (S.lower.coordinate 1)
      (1 - S.upper.coordinate 1)) forward
    have upper_bound := member.2
    rw [homogeneous.2] at upper_bound
    dsimp only [μ] at bound ⊢
    nlinarith

end AcuteWedgeFrame

theorem source_quadrant_of_relative_error {z w : ℂ} {μ ε : ℝ}
    (small : ε < μ) (height : 0 < z.re + z.im)
    (horizontal : μ * (z.re + z.im) ≤ z.re)
    (vertical : μ * (z.re + z.im) ≤ z.im)
    (error : ‖w - z‖ ≤ ε * (z.re + z.im)) : 0 < w.re ∧ 0 < w.im := by
  have first := (abs_le.mp ((Complex.abs_re_le_norm _).trans error)).1
  have last := (abs_le.mp ((Complex.abs_im_le_norm _).trans error)).1
  simp only [Complex.sub_re] at first
  simp only [Complex.sub_im] at last
  have gap := mul_pos (sub_pos.mpr small) height
  constructor <;> nlinarith

end Unfoldings
