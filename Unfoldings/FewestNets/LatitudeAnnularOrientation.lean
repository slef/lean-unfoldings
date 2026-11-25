module

public import Unfoldings.FewestNets.LatitudeChordBase
public import Unfoldings.FewestNets.LatitudeFrameOrientation
public import Unfoldings.FewestNets.LatitudeMeridionalOrientation

/-! Every annular triangle has the same signed ambient determinant in its cyclic order. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real Module

local notation "std" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin 3) ℝ)

private theorem det_symmetric_latitude_base (p q r : Space)
    (east : p 0 = -q 0) (south : p 1 = q 1) (radial : p 2 = q 2) :
    (std).det ![p, q, r] = 2 * q 0 * (r 1 * p 2 - p 1 * r 2) := by
  rw [Basis.det_apply, Matrix.det_fin_three]
  simp only [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr]
  norm_num
  rw [east, south, radial]
  ring

private theorem latitudeFrame_det_triangle_neg (ell longitude : ℝ) (p q r : Space)
    (chart : 0 < (std).det ![latitudeFrame ell longitude p, latitudeFrame ell longitude q,
      latitudeFrame ell longitude r]) :
    (std).det ![p, q, r] < 0 := by
  let f := (latitudeFrame ell longitude).toLinearEquiv.toLinearMap
  have images : f ∘ ![p, q, r] = ![f p, f q, f r] := by
    funext i
    fin_cases i <;> rfl
  have signed := (std).det_comp f ![p, q, r]
  rw [images, show LinearMap.det f = -1 from latitudeFrame_det ell longitude, neg_one_mul] at signed
  exact neg_pos.mp (signed ▸ chart)

private theorem latitudeFrame_base_coordinates {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (valid : j ≤ stripCount a) (edge : Fin (rowSize a j))
    (ell : ℝ) :
    let longitude := rowMidpoint (rowSize a j) edge
    let left := latitudeFrame ell longitude (rowSite a j edge.val)
    let right := latitudeFrame ell longitude (rowSite a j (edge.val + 1))
    left 0 = -right 0 ∧ left 1 = right 1 ∧ left 2 = right 2 ∧ 0 < right 0 := by
  let k := rowSize a j
  let longitude := rowMidpoint k edge
  let half := π / (k : ℝ)
  have first : rowLongitude k edge.val = longitude + -half := by
    dsimp only [longitude, half]
    linarith only [rowMidpoint_sub_rowLongitude edge]
  have last : rowLongitude k (edge.val + 1) = longitude + half := by
    dsimp only [longitude, half]
    linarith only [rowLongitude_succ_sub_rowMidpoint edge]
  dsimp only
  unfold rowSite
  rw [first, last, latitudeFrame_site, latitudeFrame_site]
  have half_pos : 0 < half := div_pos pi_pos (Nat.cast_pos.mpr (rowSize_pos positive small valid))
  have half_small : half < π := by
    have sine := row_sine_lower positive small valid
    have sine_pos : 0 < sin (colatitude a j) := by linarith only [sine, polarRadius_pos positive]
    have cap := spacing_lt positive small
    rw [radius_eq_polarRadius] at cap
    have half_step := (longitudeStep_bounds positive small valid).2
    change 2 * π / (rowSize a j : ℝ) ≤ _ at half_step
    have same : 2 * π / (rowSize a j : ℝ) = 2 * half := by dsimp [half, k]; ring
    rw [same] at half_step
    have step := (le_div_iff₀ sine_pos).mp half_step
    by_contra! large
    have bad := mul_le_mul_of_nonneg_right large sine_pos.le
    have pi := mul_lt_mul_of_pos_right pi_gt_d2 sine_pos
    nlinarith only [step, bad, cap, sine, pi, polarRadius_pos positive]
  have row_range := colatitude_mem positive small valid
  have east_pos := mul_pos (sin_pos_of_pos_of_lt_pi row_range.1 row_range.2)
    (sin_pos_of_pos_of_lt_pi half_pos half_small)
  exact ⟨by simp [sin_neg], by simp [cos_neg], by simp [latitudeDenominator, cos_neg], east_pos⟩

/-- The actual lower advance has negative ambient determinant in its cyclic order. -/
theorem latitude_lowerAdvance_det_neg {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (strip : j < stripCount a) (edge : Fin (rowSize a j)) (apex : ℕ)
    (nearest : |rowMidpoint (rowSize a j) edge - rowLongitude (rowSize a (j + 1)) apex|
      ≤ π / rowSize a (j + 1)) :
    (std).det ![rowSite a j edge.val, rowSite a j (edge.val + 1),
      rowSite a (j + 1) apex] < 0 := by
  let longitude := rowMidpoint (rowSize a j) edge
  let ell := chartColatitude a j
  obtain ⟨east, south, radial, pos⟩ := latitudeFrame_base_coordinates positive small strip.le edge ell
  have area := latitude_strip_meridional_cross_pos positive small strip longitude edge.val apex
    (rowMidpoint_closest_left edge) nearest
  apply latitudeFrame_det_triangle_neg ell longitude
  rw [det_symmetric_latitude_base _ _ _ east south radial]
  exact mul_pos (mul_pos (by norm_num) pos) area

/-- The upper advance has the same orientation, with its base traversed in reverse. -/
theorem latitude_upperAdvance_det_neg {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (strip : j < stripCount a) (edge : Fin (rowSize a (j + 1))) (apex : ℕ)
    (nearest : |rowMidpoint (rowSize a (j + 1)) edge - rowLongitude (rowSize a j) apex|
      ≤ π / rowSize a j) :
    (std).det ![rowSite a (j + 1) (edge.val + 1), rowSite a (j + 1) edge.val,
      rowSite a j apex] < 0 := by
  let longitude := rowMidpoint (rowSize a (j + 1)) edge
  let ell := chartColatitude a j
  let p := latitudeFrame ell longitude (rowSite a (j + 1) edge.val)
  let q := latitudeFrame ell longitude (rowSite a (j + 1) (edge.val + 1))
  let r := latitudeFrame ell longitude (rowSite a j apex)
  obtain ⟨east, south, radial, pos⟩ :=
    latitudeFrame_base_coordinates positive small (Nat.succ_le_of_lt strip) edge ell
  change p 0 = -q 0 at east
  change p 1 = q 1 at south
  change p 2 = q 2 at radial
  change 0 < q 0 at pos
  have area := latitude_strip_meridional_cross_pos positive small strip longitude apex edge.val
    nearest (rowMidpoint_closest_left edge)
  change 0 < p 1 * r 2 - r 1 * p 2 at area
  have west : q 0 = -p 0 := by linarith only [east]
  have inward : r 1 * q 2 - q 1 * r 2 < 0 := by
    rw [← south, ← radial]
    linarith only [area]
  have negative : p 0 < 0 := by linarith only [east, pos]
  apply latitudeFrame_det_triangle_neg ell longitude
  change 0 < (std).det ![q, p, r]
  rw [det_symmetric_latitude_base _ _ _ west south.symm radial.symm]
  exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (by norm_num) negative) inward

/-- The derivative orientation is the same for every actual step, including ties. -/
theorem latitudeSweepChordVertices_det_neg {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (strip : j < stripCount a)
    (step : Fin (rowSize a j + rowSize a (j + 1)) ≃
      Fin (rowSize a j) ⊕ Fin (rowSize a (j + 1)))
    (sorted : StrictMono (midpointKey ∘ step)) (i : Fin (rowSize a j + rowSize a (j + 1))) :
    (std).det (latitudeSweepChordVertices a j step i) < 0 := by
  unfold latitudeSweepChordVertices
  rcases advance : step i with edge | edge
  · exact latitude_lowerAdvance_det_neg positive small strip edge _
      (upperSweep_near_lower_midpoint step sorted
        (rowSize_pos positive small (Nat.succ_le_of_lt strip)) i edge advance)
  · exact latitude_upperAdvance_det_neg positive small strip edge _
      (lowerSweep_near_upper_midpoint step sorted
        (rowSize_pos positive small strip.le) i edge advance)

end Unfoldings.FewestNets.AcuteLatitudeGrid
