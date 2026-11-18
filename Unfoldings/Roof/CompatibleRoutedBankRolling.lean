module

public import Unfoldings.Roof.RadialBankSubhistoryRolling
public import Unfoldings.Roof.CompatibleSubhistoryMargins

/-! Actual compatible routing supplies every physical subhistory margin needed for rolling. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v w z

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)
  {Fine : Type w} [Fintype Fine] {D : TriangleComplex.{w, z} Fine} {Q : ConvexRoof D}
  {φ η γ c : ℝ} {retain : Set D.Seam} {m : ℕ} {full : (D.boundarySystem retain).Chain m}
  {control : Plane}

/-- The physical routing and constructed comparisons force radial order on the intrinsic roll. -/
theorem intrinsicBank_globallyRadiallyMonotone
    (data : Q.RadialBankComparisons φ η γ retain full control)
    (follows : R.Follows (Q.folding.projectedBoundaryChain full))
    (positive : 0 < a) (beta : 0 ≤ β) (acute : β < Real.pi / 2)
    {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes)
    (upper : ∀ p ∈ G.slopes, ‖p‖ ≤ b)
    (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2)
    (nonnegative : 0 ≤ η) (cos_positive : 0 < c) (normal : ∀ f, c ≤ Q.normal f 2)
    (rolling : radialBlockError c⁻¹ η γ⁻¹ (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4) <
      Real.cos (2 * annularHistoryAngle (a / b) β)) :
    (D.boundaryChainRoll full).GloballyRadiallyMonotone := by
  apply data.globallyRadiallyMonotone nonnegative cos_positive normal _ rolling
  intro j i earlier
  exact R.follows_subhistory_radial_margin (Q.folding.projectedBoundaryChain full) follows
    positive beta acute bpos ratio inner_disk upper small j i earlier

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
