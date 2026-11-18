module

public import Unfoldings.Roof.SourceStartBankRolling
public import Unfoldings.Roof.CompatibleSubhistoryMargins

/-! Actual routing controls the complete original intrinsic roll from its source-starting edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v w z

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)
  {Fine : Type w} [Fintype Fine] {D : TriangleComplex.{w, z} Fine} {Q : ConvexRoof D}
  {φ η c b : ℝ} {retain : Set D.Seam} {m : ℕ} {full : (D.boundarySystem retain).Chain m}

local notation "physical" => Q.folding.projectedBoundaryChain full
local notation "gamma" => Real.cos (2 * annularHistoryAngle (a / b) β)

/-- No positive initial-distance assumption: the full original bank begins at its actual source. -/
theorem sourceStart_intrinsicBank_globallyRadiallyMonotone
    (comparisons : Q.SupportedBankWindowComparisons φ η retain full ((physical).vertex 0))
    (follows : R.Follows physical)
    (positive : 0 < a) (beta : 0 ≤ β) (acute : β < Real.pi / 2)
    (bpos : 0 < b) (ratio : a ≤ b) (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes)
    (upper : ∀ p ∈ G.slopes, ‖p‖ ≤ b)
    (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2)
    (nonnegative : 0 ≤ η) (cos_positive : 0 < c) (normal : ∀ f, c ≤ Q.normal f 2)
    (rolling : radialBlockError c⁻¹ η (gamma)⁻¹
      (Real.sqrt (1 - (gamma) ^ 2)) (Real.pi / 4) < gamma) :
    (D.boundaryChainRoll full).GloballyRadiallyMonotone := by
  have gamma_positive := fine_annular_radial_margin_pos small
  have physical_outward := R.follows_outward physical follows positive beta acute bpos ratio
    inner_disk upper small
  have radial : (physical).RadialFrom ((physical).vertex 0) 0 := by
    intro i earlier
    exact ((physical).radiallyMonotone_iff_outward.mpr physical_outward) 0 i earlier
  have all_anchors (j : Fin (m + 2)) (i : Fin (m + 1)) (earlier : j.val ≤ i.val) :
      (gamma) * (‖(physical).vertex i.castSucc - (physical).vertex j‖ * ‖(physical).edge i‖) ≤
        inner ℝ ((physical).vertex i.castSucc - (physical).vertex j) ((physical).edge i) :=
    R.follows_subhistory_radial_margin physical follows positive beta acute bpos ratio inner_disk
      upper small j i earlier
  have source_margin (i : Fin (m + 1)) :
      (gamma) * (‖(physical).vertex i.castSucc - (physical).vertex 0‖ * ‖(physical).edge i‖) ≤
        inner ℝ ((physical).vertex i.castSucc - (physical).vertex 0) ((physical).edge i) :=
    all_anchors 0 i (Nat.zero_le _)
  have ratios := Q.projectedMetricStretch_bounds cos_positive normal (full.point 0)
  have error_nonnegative := radialBlockError_nonneg (ratios.1.trans ratios.2) nonnegative
    (inv_nonneg.mpr gamma_positive.le) (Real.sqrt_nonneg (1 - (gamma) ^ 2))
    (show 0 < Real.pi / 4 from div_pos Real.pi_pos (by norm_num))
  have loss_nonnegative : 0 ≤
      ((gamma) - radialBlockError c⁻¹ η (gamma)⁻¹
        (Real.sqrt (1 - (gamma) ^ 2)) (Real.pi / 4)) /
      (1 + radialBlockError c⁻¹ η (gamma)⁻¹
        (Real.sqrt (1 - (gamma) ^ 2)) (Real.pi / 4)) :=
    div_nonneg (sub_nonneg.mpr rolling.le) (by positivity)
  have outward : (D.boundaryChainRoll full).Outward := by
    intro j i earlier
    have estimate := comparisons.sourceStart_subhistory_margin rfl gamma_positive
      (Real.cos_le_one _) radial source_margin nonnegative cos_positive normal all_anchors rolling
      j i earlier
    exact (mul_nonneg loss_nonnegative
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans estimate
  exact PolygonalChain.Outward.globallyRadiallyMonotone _ outward

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
