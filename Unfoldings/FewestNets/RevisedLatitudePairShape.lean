module

public import Unfoldings.FewestNets.RevisedLatitudeChart

/-! Shape data for two opposite sites in a common revised band chart. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real

/-- A strip is polar when either row is one of the two refined rows. -/
def isPolarStrip (a : ℝ) (j : ℕ) : Bool := isPolarRow a j || isPolarRow a (j + 1)

private theorem ordinateErrorFactor_le_or (p q : Bool) :
    ordinateErrorFactor p ≤ ordinateErrorFactor (p || q) ∧
      ordinateErrorFactor q ≤ ordinateErrorFactor (p || q) := by
  cases p <;> cases q <;> norm_num [ordinateErrorFactor]

private theorem slopeSite_ordinate_correction (a : ℝ) (strip row : ℕ) (w : ℝ) :
    let Z := latitudeDenominator (stripMidpoint a strip) (colatitude a row) w
    (slopeSite a strip row w) 1 - sin (colatitude a row - stripMidpoint a strip) / Z =
      -cos (stripMidpoint a strip) * (sin (colatitude a row) * (1 - cos w)) / Z := by
  dsimp only
  unfold slopeSite
  change ((sin (colatitude a row - stripMidpoint a strip) -
    cos (stripMidpoint a strip) * sin (colatitude a row) * (1 - cos w)) /
      latitudeDenominator (stripMidpoint a strip) (colatitude a row) w) - _ = _
  rw [← sub_div, sub_sub_cancel_left]
  ring

/-- Sites on opposite rows retain their order in every midpoint chart,
including the two polar strips. -/
theorem slopeSite_pair_shape {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    {strip : ℕ} (valid : strip < stripCount a) {w₀ w₁ : ℝ}
    (near₀ : |w₀| ≤ longitudeStep a strip / 2)
    (near₁ : |w₁| ≤ longitudeStep a (strip + 1) / 2) :
    let Y₀ := (slopeSite a strip strip w₀) 1
    let Y₁ := (slopeSite a strip (strip + 1) w₁) 1
    let polar := isPolarStrip a strip
    let r := radius a
    let hmin : ℝ := if polar then 0.815 else 0.834
    let hmax : ℝ := if polar then 1.070 else 1.051
    let ymin : ℝ := if polar then 0.393 else 0.412
    let ymax : ℝ := if polar then 0.550 else 0.531
    (hmin * r < Y₁ - Y₀ ∧ Y₁ - Y₀ < hmax * r) ∧
      (ymin * r < -Y₀ ∧ -Y₀ < ymax * r) ∧
      ymin * r < Y₁ ∧ Y₁ < ymax * r := by
  let m := stripMidpoint a strip
  let l₀ := colatitude a strip
  let l₁ := colatitude a (strip + 1)
  let Z₀ := latitudeDenominator m l₀ w₀
  let Z₁ := latitudeDenominator m l₁ w₁
  let Y₀ := (slopeSite a strip strip w₀) 1
  let Y₁ := (slopeSite a strip (strip + 1) w₁) 1
  let d := rowStep a
  let r := radius a
  let b := spacing a
  obtain ⟨lo₀, hi₀, _, close₀⟩ :=
    slopeSite_bounds positive small valid (Or.inl rfl) near₀
  obtain ⟨lo₁, hi₁, _, close₁⟩ :=
    slopeSite_bounds positive small valid (Or.inr rfl) near₁
  have z₀ : Z₀ ∈ Set.Icc (0.9612 : ℝ) 1 := ⟨lo₀.le, hi₀.trans (cos_le_one _)⟩
  have z₁ : Z₁ ∈ Set.Icc (0.9612 : ℝ) 1 := ⟨lo₁.le, hi₁.trans (cos_le_one _)⟩
  have a₀ : l₀ - m = -(d / 2) := (colatitude_sub_midpoint a strip).1
  have a₁ : l₁ - m = d / 2 := (colatitude_sub_midpoint a strip).2
  let E := ordinateErrorFactor (isPolarStrip a strip)
  have e₀ : Y₀ + sin (d / 2) / Z₀ =
      -cos m * (sin l₀ * (1 - cos w₀)) / Z₀ := by
    have equal := slopeSite_ordinate_correction a strip strip w₀
    change Y₀ - sin (l₀ - m) / Z₀ = _ at equal
    rwa [a₀, sin_neg, neg_div, sub_neg_eq_add] at equal
  have e₁ : Y₁ - sin (d / 2) / Z₁ =
      -cos m * (sin l₁ * (1 - cos w₁)) / Z₁ := by
    have equal := slopeSite_ordinate_correction a strip (strip + 1) w₁
    change Y₁ - sin (l₁ - m) / Z₁ = _ at equal
    rwa [a₁] at equal
  have factor := ordinateErrorFactor_le_or (isPolarRow a strip) (isPolarRow a (strip + 1))
  have err₀ : |Y₀ + sin (d / 2) / Z₀| ≤ E * b ^ 2 / r := by
    change |Y₀ - sin (l₀ - m) / Z₀| ≤ ordinateErrorFactor (isPolarRow a strip) * b ^ 2 / r at close₀
    rw [a₀, sin_neg, neg_div, sub_neg_eq_add] at close₀
    exact close₀.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right factor.1 (sq_nonneg b)) (radius_pos positive).le)
  have err₁ : |Y₁ - sin (d / 2) / Z₁| ≤ E * b ^ 2 / r := by
    change |Y₁ - sin (l₁ - m) / Z₁| ≤ ordinateErrorFactor (isPolarRow a (strip + 1)) * b ^ 2 / r at close₁
    rw [a₁] at close₁
    exact close₁.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right factor.2 (sq_nonneg b)) (radius_pos positive).le)
  have sign : 0 ≤ (Y₀ + sin (d / 2) / Z₀) * (Y₁ - sin (d / 2) / Z₁) := by
    rw [e₀, e₁]
    have first : 0 ≤ sin l₀ * (1 - cos w₀) := mul_nonneg
      (sin_pos_of_mem_Ioo (colatitude_mem positive small valid.le)).le
      (sub_nonneg.mpr (cos_le_one _))
    have last : 0 ≤ sin l₁ * (1 - cos w₁) := mul_nonneg
      (sin_pos_of_mem_Ioo (colatitude_mem positive small (Nat.succ_le_of_lt valid))).le
      (sub_nonneg.mpr (cos_le_one _))
    have p₀ : 0 ≤ Z₀ := by linarith only [z₀.1]
    have p₁ : 0 ≤ Z₁ := by linarith only [z₁.1]
    rcases le_total 0 (-cos m) with side | side
    · exact mul_nonneg (div_nonneg (mul_nonneg side first) p₀) (div_nonneg (mul_nonneg side last) p₁)
    · exact mul_nonneg_of_nonpos_of_nonpos (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg side first) p₀)
        (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg side last) p₁)
  have bounds := rowStep_bounds positive small
  exact triangle_height_bounds (isPolarStrip a strip) (radius_pos positive) (radius_lt small)
    (spacing_pos positive) (spacing_lt positive small) bounds.1.le bounds.2 z₀ z₁ err₀ err₁ sign

end Unfoldings.FewestNets.RevisedLatitudeGrid
