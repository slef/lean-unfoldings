module

public import Unfoldings.FewestNets.RevisedLatitudeRows
public import Unfoldings.FewestNets.RoundSelectorDevelopment
public import Unfoldings.Geometry.RegularPolygonSelector

/-! Unfolding components selected by either refined polar polygon. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real

/-- The refined polar mesh gives sufficient aperture beyond the old numerical scale. -/
theorem polar_aperture {a x : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (nonnegative : 0 ≤ x) (sixth : x ≤ π / 6) (mesh : x ≤ 1.33 * a) :
    1 / (√2 * cos x) < cos (π / 4 - 0.49 * a) := by
  have amax : a ≤ 0.524 := by linarith only [small, pi_lt_d4]
  have sinx : 0 ≤ sin x :=
    sin_nonneg_of_nonneg_of_le_pi nonnegative (by linarith only [sixth, pi_pos])
  have sine := sin_sq_add_cos_sq x
  have sa : 0 < 0.98 * a := by positivity
  have sin_lower : 0.93 * a < sin (0.98 * a) := by
    have s := pow_le_pow_left₀ sa.le (show 0.98 * a ≤ 0.514 by linarith only [amax]) 2
    have cube := mul_le_mul_of_nonneg_right s sa.le
    nlinarith only [sin_gt_sub_cube sa, cube, positive]
  have product : sin x ^ 2 < sin (0.98 * a) * cos x ^ 2 := by
    by_cases low : a ≤ 0.35
    · have r1 := pow_le_pow_left₀ sinx (Real.sin_le nonnegative) 2
      have r2 := pow_le_pow_left₀ nonnegative mesh 2
      have a2 : a ^ 2 ≤ 0.35 * a := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right low positive.le
      have s2 : sin x ^ 2 ≤ 0.62 * a := by
        nlinarith only [r1, r2, a2, positive]
      have c2 : 0.78 ≤ cos x ^ 2 := by linarith only [s2, low, sine]
      have bound := mul_le_mul_of_nonneg_left c2 (show 0 ≤ sin (0.98 * a) by linarith only [sin_lower, positive])
      linarith only [s2, bound,
        mul_lt_mul_of_pos_right sin_lower (by norm_num : (0 : ℝ) < 0.78), positive]
    · have s : sin x ≤ 1 / 2 := by
        rw [← sin_pi_div_six]
        exact sin_le_sin_of_le_of_le_pi_div_two (by linarith only [nonnegative, pi_pos])
          (by linarith only [pi_pos]) sixth
      have sq := pow_le_pow_left₀ sinx s 2
      have c2 : 3 / 4 ≤ cos x ^ 2 := by linarith only [sq, sine]
      have lower : (1 : ℝ) / 3 < sin (0.98 * a) := by
        calc
          _ < sin 0.343 := by
            have h := sin_gt_sub_cube (show (0 : ℝ) < 0.343 by norm_num)
            linarith only [h]
          _ ≤ _ := sin_le_sin_of_le_of_le_pi_div_two (by linarith only [pi_pos])
            (by linarith only [small, pi_pos]) (by linarith only [lt_of_not_ge low])
      have bound := mul_le_mul_of_nonneg_left c2 (show 0 ≤ sin (0.98 * a) by linarith only [lower])
      linarith only [sq, bound,
        mul_lt_mul_of_pos_right lower (by norm_num : (0 : ℝ) < 3 / 4)]
  have enough : 1 < (1 + sin (0.98 * a)) * cos x ^ 2 := by
    nlinarith only [product, sine]
  have cos_id : 2 * cos (π / 4 - 0.49 * a) ^ 2 = 1 + sin (0.98 * a) := by
    have double := cos_two_mul (π / 4 - 0.49 * a)
    rw [show 2 * (π / 4 - 0.49 * a) = π / 2 - 0.98 * a by ring, cos_pi_div_two_sub] at double
    linarith only [double]
  have cx : 0 < cos x := cos_pos_of_mem_Ioo
    ⟨by linarith only [nonnegative, pi_pos], by linarith only [sixth, pi_pos]⟩
  have ca : 0 < cos (π / 4 - 0.49 * a) := cos_pos_of_mem_Ioo
    ⟨by linarith only [small, pi_pos], by linarith only [positive, pi_pos]⟩
  apply (sq_lt_sq₀ (by positivity : 0 ≤ 1 / (√2 * cos x)) ca.le).mp
  rw [div_pow, one_pow, mul_pow, sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  apply (div_lt_iff₀ (by positivity)).mpr
  rw [← cos_id] at enough
  nlinarith only [enough]

end Unfoldings.FewestNets.RevisedLatitudeGrid

namespace Unfoldings.ConvexRoof

open Real FewestNets RevisedLatitudeGrid

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C)

/-- An original-edge net for every selected component of a refined polar polygon. -/
theorem hasOriginalEdgeNet_of_revisedLatitudePolarSelector (frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (generic : ∀ f, K.normalSlope f ∉ frontier
      (regularSlopePolygon frame (polarSize a) (tan (AcuteLatitudeGrid.polarRadius a))))
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ π / 2 - a) :
    let slopes := regularSlopePolygon frame (polarSize a) (tan (AcuteLatitudeGrid.polarRadius a))
    ∀ seed, K.normalSlope seed ∈ slopes → C.HasOriginalEdgeNet (K.selectionComponent slopes seed) := by
  let k := polarSize a
  let x := π / (k : ℝ)
  let φ := AcuteLatitudeGrid.polarRadius a
  obtain ⟨six, _, mesh⟩ := polarSize_bounds positive small
  have enough : 3 ≤ k := le_trans (by decide : 3 ≤ 6) six
  have k_pos : 0 < k := Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le (by decide : 0 < 3) enough)
  let : Nonempty (Fin k) := ⟨⟨0, k_pos⟩⟩
  have xp : 0 ≤ x := div_nonneg pi_pos.le (Nat.cast_nonneg k)
  have x_upper : x ≤ π / 6 := div_le_div_of_nonneg_left pi_pos.le
    (by norm_num) (by exact_mod_cast six)
  have phi_pos : 0 < φ := AcuteLatitudeGrid.polarRadius_pos positive
  have phi_lt : φ < π / 2 := by
    dsimp only [φ]
    linarith only [AcuteLatitudeGrid.polarRadius_lt small, pi_gt_d2]
  have rad : 0 < tan φ := tan_pos_of_pos_of_lt_pi_div_two phi_pos phi_lt
  have tilt_sq : φ ^ 2 ≤ a / 144 := by
    unfold φ AcuteLatitudeGrid.polarRadius
    rw [div_pow, sq_sqrt positive.le]
    norm_num
  exact K.hasOriginalEdgeNet_of_roundSelector_of_aperture
    (regularPolygonSideDirections frame enough rad) positive small phi_pos tilt_sq
    xp x_upper (polar_aperture positive small xp x_upper mesh.le)
    (acute_polar_exit_margin small xp x_upper)
    (fun _ => rfl) (fun _ => norm_le_of_mem_regularSlopePolygon frame enough) generic angles

end Unfoldings.ConvexRoof
