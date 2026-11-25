module

public import Unfoldings.FewestNets.RoundSelectorDevelopment
public import Unfoldings.Geometry.RegularPolygonSelector

/-! The polar cells at the actual latitude-grid scale meet the round selector theorem. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Real FewestNets

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C)

/-- At either pole the first and last ring have this same size and radius.
Each selected component has a genuine original-edge net. -/
theorem hasOriginalEdgeNet_of_latitudePolarSelector (frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (generic : ∀ f, K.normalSlope f ∉ frontier
      (regularSlopePolygon frame (latitudeRowSize a 0) (tan (latitudeRadius a / 2))))
    (angles : ∀ f, ∀ i, (C.triangle f).cornerAngle i ≤ π / 2 - a) :
    let slopes := regularSlopePolygon frame (latitudeRowSize a 0) (tan (latitudeRadius a / 2))
    ∀ seed, K.normalSlope seed ∈ slopes → C.HasOriginalEdgeNet (K.selectionComponent slopes seed) := by
  let k := latitudeRowSize a 0
  let phi := latitudeRadius a / 2
  let x := π / (k : ℝ)
  have savings := latitude_polar_size_bounds positive small
  have bound : (3 : ℝ) < (k : ℝ) := by
    have lower : (3 : ℝ) ≤ 0.999 * π / (0.45 * a) := by
      apply (le_div_iff₀ (by positivity : 0 < 0.45 * a)).mpr
      linarith only [small, pi_pos]
    exact lower.trans_lt savings.1
  have enough : 3 ≤ k := by
    have casted : 3 ≤ (k : ℝ) := bound.le
    exact_mod_cast casted
  have kp : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have xp : 0 ≤ x := div_nonneg pi_pos.le kp.le
  have x_upper : x ≤ √a / 2 := (savings.2.2.1.trans savings.2.2.2).le
  have mesh : x ^ 2 ≤ a / 4 := calc
    _ ≤ (√a / 2) ^ 2 := pow_le_pow_left₀ xp x_upper 2
    _ = _ := by rw [div_pow, sq_sqrt positive.le]; norm_num
  have tilt_pos : 0 < phi := div_pos (latitudeRadius_pos positive) (by norm_num)
  have tilt_lt : phi < π / 2 := by
    have r_upper := latitudeRadius_lt small
    dsimp only [phi]
    linarith only [r_upper, pi_gt_d2]
  have radius_pos : 0 < tan phi := by
    rw [tan_eq_sin_div_cos]
    exact div_pos (sin_pos_of_pos_of_lt_pi tilt_pos (by linarith only [tilt_lt, pi_pos]))
      (cos_pos_of_mem_Ioo ⟨by linarith only [tilt_pos, pi_pos], tilt_lt⟩)
  have tilt_sq : phi ^ 2 ≤ a / 144 := by
    have eq : phi = (2 / 25 : ℝ) * √a := by simp [phi, latitudeRadius]; ring
    rw [eq, mul_pow, sq_sqrt positive.le]
    nlinarith only [positive]
  exact K.hasOriginalEdgeNet_of_roundSelector
    (regularPolygonSideDirections frame enough radius_pos) positive small tilt_pos tilt_sq xp mesh
    (fun _ => rfl) (fun _ => norm_le_of_mem_regularSlopePolygon frame enough) generic angles

end Unfoldings.ConvexRoof
