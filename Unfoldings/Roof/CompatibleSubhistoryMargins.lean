module

public import Unfoldings.Roof.CompatibleFineMargins
public import Unfoldings.Geometry.AnnularFineMargin
public import Unfoldings.Geometry.ChainInterval
public import Unfoldings.Geometry.RadialChainPoints

/-! All compatible subhistories have the same fine-vertex margin and whole-point radial order. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

variable {n : ℕ} (P : PolygonalChain Plane n) (follows : R.Follows P)

include follows

theorem follows_interval (first length : ℕ) (fits : first + length ≤ n) :
    R.Follows (P.interval first length fits) := by
  intro i
  exact follows ⟨first + i.val, by omega⟩

variable (positive : 0 < a) (beta : 0 ≤ β) (acute : β < Real.pi / 2)
  {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
  (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes)
  (upper : ∀ p ∈ G.slopes, ‖p‖ ≤ b)
  (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2)

include positive beta acute bpos ratio inner_disk upper small

/-- Every earlier fine anchor has the same quantitative bound against every later actual edge. -/
theorem follows_subhistory_radial_margin (j : Fin (n + 1)) (i : Fin n)
    (earlier : j.val ≤ i.val) :
    Real.cos (2 * annularHistoryAngle (a / b) β) *
      (‖P.vertex i.castSucc - P.vertex j‖ * ‖P.edge i‖) ≤
        inner ℝ (P.vertex i.castSucc - P.vertex j) (P.edge i) := by
  let fits : j.val + (i.val - j.val) ≤ n := by omega
  let A := P.interval j.val (i.val - j.val) fits
  have first : A.vertex 0 = P.vertex j := by rfl
  have last : A.vertex (Fin.last (i.val - j.val)) = P.vertex i.castSucc := by
    change P.vertex ⟨j.val + (i.val - j.val), by omega⟩ = _
    congr 1
    apply Fin.ext
    change j.val + (i.val - j.val) = i.val
    omega
  have step : R.FollowsStep (A.vertex (Fin.last (i.val - j.val))) (P.vertex i.succ) := by
    rw [last]
    exact follows i
  have margin := R.follows_radial_margin_at_fine_step positive beta acute bpos ratio inner_disk
    upper small A (R.follows_interval P follows _ _ fits) (P.vertex i.succ) step
  rw [first, last] at margin
  exact margin

/-- Every compatible fine path is radially monotone from every earlier vertex. -/
theorem follows_outward : P.Outward := by
  intro j i earlier
  have margin := R.follows_subhistory_radial_margin P follows positive beta acute bpos ratio
    inner_disk upper small j i earlier
  exact (mul_nonneg (fine_annular_radial_margin_pos small).le
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans margin

/-- The order holds from arbitrary earlier points inside fine edges, not just at vertices. -/
theorem follows_globallyRadiallyMonotone : P.GloballyRadiallyMonotone :=
  PolygonalChain.Outward.globallyRadiallyMonotone P
    (R.follows_outward P follows positive beta acute bpos ratio inner_disk upper small)

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
