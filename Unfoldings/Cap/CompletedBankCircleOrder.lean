module

public import Unfoldings.Cap.CompletedBankChainOrder
public import Unfoldings.Geometry.BankRadialOrder

/-! Opposite actual branching banks have the correct order on common-source circles. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

/-- The center can be the common developed source, rather than the leaf of this path.
No radial monotonicity of the jumps at intermediate branches is assumed. -/
theorem chain_circle_order {n : ℕ} (i : FiveSector)
    (chain : Fin n → {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (parents : ∀ j k : Fin n, k.val = j.val + 1 →
      N.spanningCompletion.parents.parent (chain j).val = (chain k).val)
    (sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (chain j))
    (directions : ∀ j, K.projectedVertex (N.spanningCompletion.parents.parent (chain j).val) -
      K.projectedVertex (chain j).val ∈ closedFiveSector t i)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (center : Plane) (j k : Fin n) (s r : unitInterval)
    (left_quadrant :
      0 ≤ (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).re ∧
      0 ≤ (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).im)
    (right_quadrant :
      0 ≤ (B.sectorFrame i (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).re ∧
      0 ≤ (B.sectorFrame i (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).im)
    (same_radius : ‖N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center‖ =
      ‖N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center‖) :
    (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).re ≤
        (B.sectorFrame i (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).re ∧
      (B.sectorFrame i (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)).im ≤
        (B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)).im := by
  let a := B.sectorFrame i (N.parentExitPoint D (chain j) (1 - (s : ℝ)) - center)
  let b := B.sectorFrame i (N.parentEntrancePoint D (chain k) (1 - (r : ℝ)) - center)
  have norm_equal : ‖a‖ = ‖b‖ := by
    simpa only [a, b, (B.sectorFrame i).norm_map] using same_radius
  have identity (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have radii : a.re ^ 2 + a.im ^ 2 = b.re ^ 2 + b.im ^ 2 := by
    rw [← identity, ← identity, norm_equal]
  have alternative := B.chain_left_or_above i chain parents sectors directions budget j k s r
  have relative : a.re ≤ b.re ∨ b.im ≤ a.im := by
    simpa only [a, b, map_sub, Complex.sub_re, Complex.sub_im, sub_le_sub_iff_right]
      using alternative
  exact quadrant_circle_order left_quadrant.1 left_quadrant.2 right_quadrant.1 right_quadrant.2
    radii relative

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
