module

public import Unfoldings.Roof.SourceStartBankRolling
public import Unfoldings.Roof.CompatibleSubhistoryMargins

/-! Positive quantitative margins survive on complete source-starting routed intrinsic banks. -/

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

/-- Actual routing supplies every physical anchor margin for the complete source bank. -/
theorem sourceStart_intrinsicBank_subhistory_margin
    (comparisons : Q.SupportedBankWindowComparisons φ η retain full ((physical).vertex 0))
    (follows : R.Follows physical)
    (positive : 0 < a) (beta : 0 ≤ β) (acute : β < Real.pi / 2)
    (bpos : 0 < b) (ratio : a ≤ b) (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes)
    (upper : ∀ p ∈ G.slopes, ‖p‖ ≤ b)
    (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2)
    (nonnegative : 0 ≤ η) (cos_positive : 0 < c) (normal : ∀ f, c ≤ Q.normal f 2)
    (rolling : radialBlockError c⁻¹ η (gamma)⁻¹
      (Real.sqrt (1 - (gamma) ^ 2)) (Real.pi / 4) < gamma)
    (j : Fin (m + 2)) (i : Fin (m + 1)) (earlier : j.val ≤ i.val) :
    ((gamma - radialBlockError c⁻¹ η (gamma)⁻¹
        (Real.sqrt (1 - (gamma) ^ 2)) (Real.pi / 4)) /
      (1 + radialBlockError c⁻¹ η (gamma)⁻¹
        (Real.sqrt (1 - (gamma) ^ 2)) (Real.pi / 4))) *
      (‖(D.boundaryChainRoll full).vertex i.castSucc - (D.boundaryChainRoll full).vertex j‖ *
        ‖(D.boundaryChainRoll full).edge i‖) ≤
      inner ℝ ((D.boundaryChainRoll full).vertex i.castSucc - (D.boundaryChainRoll full).vertex j)
        ((D.boundaryChainRoll full).edge i) := by
  have gamma_positive := fine_annular_radial_margin_pos small
  have physical_outward := R.follows_outward physical follows positive beta acute bpos ratio
    inner_disk upper small
  have radial : (physical).RadialFrom ((physical).vertex 0) 0 := by
    intro k earlier
    exact ((physical).radiallyMonotone_iff_outward.mpr physical_outward) 0 k earlier
  have anchors (k : Fin (m + 2)) (l : Fin (m + 1)) (before : k.val ≤ l.val) :
      gamma * (‖(physical).vertex l.castSucc - (physical).vertex k‖ * ‖(physical).edge l‖) ≤
        inner ℝ ((physical).vertex l.castSucc - (physical).vertex k) ((physical).edge l) :=
    R.follows_subhistory_radial_margin physical follows positive beta acute bpos ratio inner_disk
      upper small k l before
  exact comparisons.sourceStart_subhistory_margin rfl gamma_positive (Real.cos_le_one _)
    radial (fun k => anchors 0 k (Nat.zero_le _)) nonnegative cos_positive normal anchors rolling
    j i earlier

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
