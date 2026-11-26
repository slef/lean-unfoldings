module

public import Unfoldings.FewestNets.RevisedLatitudeOrientedChart
public import Unfoldings.FewestNets.RevisedLatitudeRouting

/-! Routing bounds on the literal reoriented annular selector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real Cap

variable {a : ℝ} {positive : 0 < a} {small : a ≤ π / 6} {i : AnnularTriangle a}
  (D : AnnularChartData positive small i)

private theorem widthFactor_le_one (b : Bool) : widthFactor b ≤ 1 := by
  cases b <;> norm_num [widthFactor]

/-- Every point of the triangle stays in the coordinate rectangle of its vertices. -/
theorem AnnularChartData.coordinate_bounds {p : Plane}
    (inside : p ∈ latitudeSlopeTriangle (-D.halfBase) D.halfBase D.base D.apex D.height) :
    |p 0| ≤ spacing a / (2 * 0.9612) ∧
      |p 1| ≤ ordinateBound a (isPolarStrip a i.1.val) := by
  let X := spacing a / (2 * 0.9612)
  let Y := ordinateBound a (isPolarStrip a i.1.val)
  let S : Set ℂ := {z | z.re ∈ Set.Icc (-X) X ∧ z.im ∈ Set.Icc (-Y) Y}
  have convex : Convex ℝ S :=
    ((convex_Icc (-X) X).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Icc (-Y) Y).linear_preimage Complex.imCLM.toLinearMap)
  let L : ℂ := ⟨-D.halfBase, D.base⟩
  let R : ℂ := ⟨D.halfBase, D.base⟩
  let A : ℂ := ⟨D.apex, D.base - D.height⟩
  have bound : |D.halfBase| ≤ X :=
    D.halfBase_bound.le.trans (div_le_div_of_nonneg_right
      (mul_le_of_le_one_left (spacing_pos positive).le (widthFactor_le_one _)) (by norm_num))
  have l : L ∈ S := ⟨abs_le.mp (show |-D.halfBase| ≤ X by rwa [abs_neg]), abs_le.mp D.base_ordinate⟩
  have r : R ∈ S := ⟨abs_le.mp bound, abs_le.mp D.base_ordinate⟩
  have a : A ∈ S := ⟨abs_le.mp D.apex_bound.le, abs_le.mp D.apex_ordinate⟩
  have hull : exitHeadingChart false p ∈ convexHull ℝ {A, L, R} := inside
  have box := convexHull_min (show ({A, L, R} : Set ℂ) ⊆ S by
    intro z h
    rcases h with eq | eq | eq <;> exact eq.symm ▸ ‹_ ∈ S›) convex hull
  have geometry : (exitHeadingChart false p).re ∈ Set.Icc (-X) X ∧
      (exitHeadingChart false p).im ∈ Set.Icc (-Y) Y := box
  simp only [exitHeadingChart_re, exitHeadingChart_im, Bool.false_eq_true, ite_false] at geometry
  exact ⟨abs_le.mpr geometry.1, abs_le.mpr geometry.2⟩

/-- The full triangle is within the tilt bound used by the projected route. -/
theorem AnnularChartData.exists_tilt :
    ∃ φ : ℝ, 0 < φ ∧ φ ≤ 0.297 ∧
      0.512 * φ ^ 2 ≤ a * distortionFactor (isPolarStrip a i.1.val) (relativeStep a) ∧
      ∀ p ∈ latitudeSlopeTriangle (-D.halfBase) D.halfBase D.base D.apex D.height, ‖p‖ ≤ tan φ := by
  obtain ⟨φ, φp, φs, err, tsq⟩ := rectangle_tilt positive small (isPolarStrip a i.1.val)
  refine ⟨φ, φp, φs, err, ?_⟩
  intro p inside
  have b := D.coordinate_bounds inside
  have t := tan_nonneg_of_nonneg_of_le_pi_div_two φp.le
    (by linarith only [φs, pi_gt_d2])
  apply (sq_le_sq₀ (norm_nonneg _) t).mp
  rw [← tsq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have one := pow_le_pow_left₀ (abs_nonneg _) b.1 2
  have two := pow_le_pow_left₀ (abs_nonneg _) b.2 2
  rw [sq_abs] at one two
  exact add_le_add one two

private theorem AnnularChartData.normalize_displacement (τ u : ℝ) (nonnegative : 0 ≤ τ)
    (bound : u ≤ τ * spacing a / 0.9612) :
    u / D.height ≤ τ * (a * apexFactor (isPolarStrip a i.1.val) (relativeStep a)) := by
  let d := heightDenominator (isPolarStrip a i.1.val) (relativeStep a)
  have dp : 0 < d := heightDenominator_relativeStep_pos positive small _
  have scale := D.height_lower
  change d * radius a ≤ 0.9612 * D.height at scale
  have rhs : τ * (a * apexFactor (isPolarStrip a i.1.val) (relativeStep a)) = τ * a * 0.51 / d := by
    unfold apexFactor
    dsimp only [d]
    ring
  rw [rhs]
  apply (div_le_div_iff₀ D.height_pos dp).mpr
  have left := mul_le_mul_of_nonneg_right bound dp.le
  have right := mul_le_mul_of_nonneg_left scale
    (show 0 ≤ τ * a * 0.51 by positivity)
  unfold spacing at left
  ring_nf at left right ⊢
  nlinarith only [left, right]

/-- The three actual side deviations use the normalized routing scalars. -/
theorem AnnularChartData.side_ratios :
    (D.halfBase - (-D.halfBase)) / D.height ≤
      a * apexFactor (isPolarStrip a i.1.val) (relativeStep a) ∧
    |latitudeEastRatio D.halfBase D.apex D.height| ≤
      a * sideFactor (isPolarStrip a i.1.val) (relativeStep a) ∧
    |latitudeWestRatio (-D.halfBase) D.apex D.height| ≤
      a * sideFactor (isPolarStrip a i.1.val) (relativeStep a) := by
  let polar := isPolarStrip a i.1.val
  let τ : ℝ := if polar then 0.8 else 1
  have tp : 0 ≤ τ := by simp only [τ]; split_ifs <;> norm_num
  have east : |D.apex - D.halfBase| ≤ τ * spacing a / 0.9612 :=
    (abs_sub _ _).trans D.horizontal_displacement
  have west : |D.apex - (-D.halfBase)| ≤ τ * spacing a / 0.9612 := by
    rw [sub_neg_eq_add]
    exact (abs_add_le _ _).trans D.horizontal_displacement
  have base := D.normalize_displacement 1 (D.halfBase - (-D.halfBase)) zero_le_one (by
    rw [sub_neg_eq_add, ← two_mul, one_mul]
    exact D.base_upper.le)
  constructor
  · simpa only [one_mul] using base
  constructor
  · rw [latitudeEastRatio, abs_div, abs_of_pos D.height_pos]
    have b := D.normalize_displacement τ _ tp east
    unfold sideFactor
    exact b.trans_eq (by dsimp only [τ, polar]; ring)
  · rw [latitudeWestRatio, abs_div, abs_of_pos D.height_pos]
    have b := D.normalize_displacement τ _ tp west
    unfold sideFactor
    exact b.trans_eq (by dsimp only [τ, polar]; ring)

end Unfoldings.FewestNets.RevisedLatitudeGrid
