module

public import Unfoldings.FewestNets.RevisedLatitudePairShape
public import Unfoldings.FewestNets.LatitudeRingsPartition
public import Unfoldings.FewestNets.LatitudeFrameOrientation

/-! The signed heights orient the actual midpoint triangles of the revised partition. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real Module

local notation "std" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin 3) ℝ)

variable {a : ℝ}

private theorem det_symmetric_base (p q r : Space)
    (horizontal : p 0 = -q 0) (meridional : p 1 = q 1) (height : p 2 = q 2) :
    (std).det ![p, q, r] = 2 * q 0 * (r 1 * p 2 - p 1 * r 2) := by
  rw [Basis.det_apply, Matrix.det_fin_three]
  simp only [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr]
  norm_num
  rw [horizontal, meridional, height]
  ring

private theorem negative_det_of_chart (ell lon : ℝ) (p q r : Space)
    (positive : 0 < (std).det ![latitudeFrame ell lon p, latitudeFrame ell lon q,
      latitudeFrame ell lon r]) :
    (std).det ![p, q, r] < 0 := by
  let f := (latitudeFrame ell lon).toLinearEquiv.toLinearMap
  have images : f ∘ ![p, q, r] = ![f p, f q, f r] := by
    funext i
    fin_cases i <;> rfl
  have signed := (std).det_comp f ![p, q, r]
  rw [images, show LinearMap.det f = -1 from latitudeFrame_det ell lon, neg_one_mul] at signed
  exact neg_pos.mp (signed ▸ positive)

private theorem raw_row_signs (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (valid : j < stripCount a) (longitude : ℝ) {w₀ w₁ : ℝ}
    (near₀ : |w₀| ≤ longitudeStep a j / 2) (near₁ : |w₁| ≤ longitudeStep a (j + 1) / 2) :
    let ℓ := stripMidpoint a j
    let p := latitudeFrame ℓ longitude (latitudeSite (colatitude a j) (longitude + w₀))
    let q := latitudeFrame ℓ longitude (latitudeSite (colatitude a (j + 1)) (longitude + w₁))
    p 1 < 0 ∧ 0 < p 2 ∧ 0 < q 1 ∧ 0 < q 2 := by
  have z₀ := (slopeSite_bounds positive small valid (Or.inl rfl) near₀).1
  have z₁ := (slopeSite_bounds positive small valid (Or.inr rfl) near₁).1
  have h := slopeSite_pair_shape positive small valid near₀ near₁
  let ymin : ℝ := if isPolarStrip a j then 0.393 else 0.412
  have yp : 0 < ymin := by
    by_cases h : isPolarStrip a j <;> norm_num [ymin, h]
  have low : (slopeSite a j j w₀) 1 < 0 := neg_pos.mp
    ((mul_pos yp (radius_pos positive)).trans h.2.1.1)
  have high : 0 < (slopeSite a j (j + 1) w₁) 1 :=
    (mul_pos yp (radius_pos positive)).trans h.2.2.1
  dsimp only
  rw [latitudeFrame_site, latitudeFrame_site]
  have zpos₀ := (show (0 : ℝ) < 0.9612 by norm_num).trans z₀
  have zpos₁ := (show (0 : ℝ) < 0.9612 by norm_num).trans z₁
  refine ⟨?_, zpos₀, (div_pos_iff_of_pos_right zpos₁).mp high, zpos₁⟩
  have raw : (sin (colatitude a j - stripMidpoint a j) -
      cos (stripMidpoint a j) * sin (colatitude a j) * (1 - cos w₀)) /
        latitudeDenominator (stripMidpoint a j) (colatitude a j) w₀ < 0 := low
  change sin (colatitude a j - stripMidpoint a j) -
    cos (stripMidpoint a j) * sin (colatitude a j) * (1 - cos w₀) < 0
  simpa only [zero_mul] using (div_lt_iff₀ zpos₀).mp raw

private theorem symmetric_base (positive : 0 < a) (small : a ≤ π / 6)
    {row : ℕ} (valid : row ≤ stripCount a) (e : Fin (rowSize a row)) (ell : ℝ) :
    let t := rowMidpoint (rowSize a row) e
    let p := latitudeFrame ell t ((rings a).rowSite row e.val)
    let q := latitudeFrame ell t ((rings a).rowSite row (e.val + 1))
    p 0 = -q 0 ∧ p 1 = q 1 ∧ p 2 = q 2 ∧ 0 < q 0 := by
  let k := rowSize a row
  let h := π / (k : ℝ)
  let t := rowMidpoint k e
  have left : rowLongitude k e.val = t + -h := by
    dsimp only [t, h]
    linarith only [rowMidpoint_sub_rowLongitude e]
  have right : rowLongitude k (e.val + 1) = t + h := by
    dsimp only [t, h]
    linarith only [rowLongitude_succ_sub_rowMidpoint e]
  have hp : 0 < h := div_pos pi_pos (Nat.cast_pos.mpr (rowSize_pos positive small valid))
  have hs : h < π := by
    have step := (longitudeStep_pos_lt_pi positive small valid).2
    change 2 * π / (k : ℝ) < π at step
    rw [show 2 * π / (k : ℝ) = 2 * h by dsimp only [h]; ring] at step
    linarith only [step, pi_pos]
  dsimp only
  change let p := latitudeFrame ell t (latitudeSite (colatitude a row) (rowLongitude k e.val))
    let q := latitudeFrame ell t (latitudeSite (colatitude a row) (rowLongitude k (e.val + 1)))
    p 0 = -q 0 ∧ p 1 = q 1 ∧ p 2 = q 2 ∧ 0 < q 0
  rw [left, right]
  dsimp only
  rw [latitudeFrame_site, latitudeFrame_site]
  exact ⟨by simp [sin_neg], by simp [cos_neg], by simp [latitudeDenominator, cos_neg],
    mul_pos (sin_pos_of_mem_Ioo (colatitude_mem positive small valid))
      (sin_pos_of_pos_of_lt_pi hp hs)⟩

private theorem lowerAdvance_det_neg (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (valid : j < stripCount a) (edge : Fin (rowSize a j)) (apex : ℕ)
    (nearest : |rowMidpoint (rowSize a j) edge - rowLongitude (rowSize a (j + 1)) apex| ≤
      π / rowSize a (j + 1)) :
    (std).det ![(rings a).rowSite j edge.val, (rings a).rowSite j (edge.val + 1),
      (rings a).rowSite (j + 1) apex] < 0 := by
  let t := rowMidpoint (rowSize a j) edge
  let w₀ := rowLongitude (rowSize a j) edge.val - t
  let w₁ := rowLongitude (rowSize a (j + 1)) apex - t
  let ℓ := stripMidpoint a j
  have near₀ : |w₀| ≤ longitudeStep a j / 2 := by
    change |rowLongitude (rowSize a j) edge.val - t| ≤ (2 * π / rowSize a j) / 2
    rw [abs_sub_comm, show (2 * π / (rowSize a j : ℝ)) / 2 = π / rowSize a j by ring]
    exact rowMidpoint_closest_left edge
  have near₁ : |w₁| ≤ longitudeStep a (j + 1) / 2 := by
    change |rowLongitude (rowSize a (j + 1)) apex - t| ≤ (2 * π / rowSize a (j + 1)) / 2
    rw [abs_sub_comm, show (2 * π / (rowSize a (j + 1) : ℝ)) / 2 = π / rowSize a (j + 1) by ring]
    exact nearest
  have left : t + w₀ = rowLongitude (rowSize a j) edge.val := by dsimp only [w₀]; ring
  have top : t + w₁ = rowLongitude (rowSize a (j + 1)) apex := by dsimp only [w₁]; ring
  have signs := raw_row_signs positive small valid t near₀ near₁
  dsimp only at signs
  rw [left, top] at signs
  obtain ⟨yn, zp, yp, zq⟩ := signs
  obtain ⟨sx, sy, sz, right⟩ := symmetric_base positive small valid.le edge ℓ
  apply negative_det_of_chart ℓ t
  rw [det_symmetric_base _ _ _ sx sy sz]
  exact mul_pos (mul_pos (by norm_num) right)
    (sub_pos.mpr ((mul_neg_of_neg_of_pos yn zq).trans (mul_pos yp zp)))

private theorem upperAdvance_det_neg (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (valid : j < stripCount a) (edge : Fin (rowSize a (j + 1))) (apex : ℕ)
    (nearest : |rowMidpoint (rowSize a (j + 1)) edge - rowLongitude (rowSize a j) apex| ≤
      π / rowSize a j) :
    (std).det ![(rings a).rowSite (j + 1) (edge.val + 1), (rings a).rowSite (j + 1) edge.val,
      (rings a).rowSite j apex] < 0 := by
  let t := rowMidpoint (rowSize a (j + 1)) edge
  let w₀ := rowLongitude (rowSize a j) apex - t
  let w₁ := rowLongitude (rowSize a (j + 1)) edge.val - t
  let ℓ := stripMidpoint a j
  have near₀ : |w₀| ≤ longitudeStep a j / 2 := by
    change |rowLongitude (rowSize a j) apex - t| ≤ (2 * π / rowSize a j) / 2
    rw [abs_sub_comm, show (2 * π / (rowSize a j : ℝ)) / 2 = π / rowSize a j by ring]
    exact nearest
  have near₁ : |w₁| ≤ longitudeStep a (j + 1) / 2 := by
    change |rowLongitude (rowSize a (j + 1)) edge.val - t| ≤ (2 * π / rowSize a (j + 1)) / 2
    rw [abs_sub_comm, show (2 * π / (rowSize a (j + 1) : ℝ)) / 2 = π / rowSize a (j + 1) by ring]
    exact rowMidpoint_closest_left edge
  have bottom : t + w₀ = rowLongitude (rowSize a j) apex := by dsimp only [w₀]; ring
  have left : t + w₁ = rowLongitude (rowSize a (j + 1)) edge.val := by dsimp only [w₁]; ring
  have signs := raw_row_signs positive small valid t near₀ near₁
  dsimp only at signs
  rw [bottom, left] at signs
  obtain ⟨yn, zp, yp, zq⟩ := signs
  obtain ⟨sx, sy, sz, right⟩ := symmetric_base positive small (Nat.succ_le_of_lt valid) edge ℓ
  have opposite :
      (latitudeFrame ℓ t ((rings a).rowSite (j + 1) (edge.val + 1))) 0 =
        -(latitudeFrame ℓ t ((rings a).rowSite (j + 1) edge.val)) 0 := by
    linarith only [sx]
  have neg : (latitudeFrame ℓ t ((rings a).rowSite (j + 1) edge.val)) 0 < 0 := by
    linarith only [sx, right]
  apply negative_det_of_chart ℓ t
  rw [det_symmetric_base _ _ _ opposite sy.symm sz.symm, ← sy, ← sz]
  exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (by norm_num) neg)
    (sub_neg.mpr ((mul_neg_of_neg_of_pos yn zq).trans (mul_pos yp zp)))

/-- The actual revised mesh meets the abstract spherical partition criterion. -/
theorem rings_oriented (positive : 0 < a) (small : a ≤ π / 6) : (rings a).Oriented where
  toAdmissible := rings_admissible positive small
  annular_negative := by
    rintro ⟨j, i⟩
    let s := LatitudeRings.sweepOrder (rowSize a j.val) (rowSize a (j.val + 1))
    have order := LatitudeRings.sweepOrder_sorted (rowSize a j.val) (rowSize a (j.val + 1))
    change (std).det (LatitudeRings.latitudeSweepChordVertices (rings a) j.val s i) < 0
    unfold LatitudeRings.latitudeSweepChordVertices
    rcases choose : s i with b | b
    · exact lowerAdvance_det_neg positive small j.isLt b _
        (upperSweep_near_lower_midpoint s order
          (rowSize_pos positive small (Nat.succ_le_of_lt j.isLt)) i b choose)
    · exact upperAdvance_det_neg positive small j.isLt b _
        (lowerSweep_near_upper_midpoint s order (rowSize_pos positive small j.isLt.le) i b choose)

end Unfoldings.FewestNets.RevisedLatitudeGrid
