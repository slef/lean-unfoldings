module

public import Unfoldings.FewestNets.AcuteLatitudeMetricRows
public import Unfoldings.FewestNets.AcutePolarScalars
public import Unfoldings.FewestNets.RoundSelectorDevelopment
public import Unfoldings.Geometry.RegularPolygonSelector

/-! Each selected component of either revised polar polygon has an original-edge net. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Real FewestNets AcuteLatitudeGrid

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C)

/-- The polar selectors of the revised grid satisfy all the actual adaptive
routing and development hypotheses. -/
theorem hasOriginalEdgeNet_of_acuteLatitudePolarSelector (frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (generic : ∀ f, K.normalSlope f ∉ frontier
      (regularSlopePolygon frame (rowSize a 0) (tan (polarRadius a))))
    (angles : ∀ f, ∀ i, (C.triangle f).cornerAngle i ≤ π / 2 - a) :
    let slopes := regularSlopePolygon frame (rowSize a 0) (tan (polarRadius a))
    ∀ seed, K.normalSlope seed ∈ slopes → C.HasOriginalEdgeNet (K.selectionComponent slopes seed) := by
  let k := rowSize a 0
  let x := π / (k : ℝ)
  let phi := polarRadius a
  obtain ⟨at_least_six, _, mesh⟩ := polar_size_bounds positive small
  have enough : 3 ≤ k := le_trans (by decide : 3 ≤ 6) at_least_six
  have k_pos : 0 < k := Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le (by decide : 0 < 3) enough)
  let : Nonempty (Fin k) := ⟨⟨0, k_pos⟩⟩
  have xp : 0 ≤ x := div_nonneg pi_pos.le (by positivity)
  have x_upper : x ≤ π / 6 := div_le_div_of_nonneg_left pi_pos.le
    (by norm_num) (by exact_mod_cast at_least_six)
  have phi_pos : 0 < phi := polarRadius_pos positive
  have phi_lt : phi < π / 2 := by
    change polarRadius a < _
    linarith only [polarRadius_lt small, pi_gt_d2]
  have radius_pos : 0 < tan phi := tan_pos_of_pos_of_lt_pi_div_two phi_pos phi_lt
  have tilt_sq : phi ^ 2 ≤ a / 144 := by
    unfold phi polarRadius
    rw [div_pow, sq_sqrt positive.le]
    norm_num
  exact K.hasOriginalEdgeNet_of_roundSelector_of_aperture
    (regularPolygonSideDirections frame enough radius_pos) positive small phi_pos tilt_sq
    xp x_upper (acute_polar_cone_ratio_lt positive small xp x_upper mesh.le)
    (acute_polar_exit_margin small xp x_upper)
    (fun _ => rfl) (fun _ => norm_le_of_mem_regularSlopePolygon frame enough) generic angles

end Unfoldings.ConvexRoof
