module

public import Unfoldings.Convex.FiniteDualPlanes

/-! Convexity of dual costs and actual maximizing normal cells. -/

@[expose] public section

namespace Unfoldings

namespace FiniteDual

variable {I : Type*} [Fintype I] [Nonempty I] (point : I → Plane) (level : I → ℝ)

theorem convex_cost : ConvexOn ℝ Set.univ (cost point level) := by
  have convex := (AffineEnvelope.concave_height (negativePlane point level)).neg
  have identity : -AffineEnvelope.height (negativePlane point level) = cost point level := by
    funext p
    change -AffineEnvelope.height (negativePlane point level) p = _
    rw [negative_cost, neg_neg]
  rw [identity] at convex
  exact convex

end FiniteDual

namespace SlopeEnvelope

variable (E : SlopeEnvelope)

theorem convex_active_cell (convex : Convex ℝ E.slopes)
    (dual_convex : ConvexOn ℝ Set.univ E.dual) (x : Plane) :
    Convex ℝ {p | E.Active x p} := by
  intro p hp q hq a b ha hb total
  have member := convex hp.1 hq.1 ha hb total
  refine ⟨member, le_antisymm ?_ (E.affine_le x member)⟩
  have dual := dual_convex.2 (Set.mem_univ p) (Set.mem_univ q) ha hb total
  change E.dual (a • p + b • q) ≤ a * E.dual p + b * E.dual q at dual
  have first := hp.2
  have last := hq.2
  dsimp [affine] at first last ⊢
  simp only [inner_add_right, real_inner_smul_right]
  have balance := congrArg (fun t : ℝ => t * E.height x) total
  simp only [add_mul, one_mul] at balance
  have first_scaled := congrArg (fun r : ℝ => a * r) first
  have last_scaled := congrArg (fun r : ℝ => b * r) last
  nlinarith

end SlopeEnvelope
end Unfoldings
