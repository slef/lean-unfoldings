module

public import Unfoldings.Cap.MatchedBankTrace

/-! Match actual parent banks directly at a positive-width physical height. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {i : FiveSector}
  {D : FacewiseDevelopment C N.completedRetain} {calibration : Plane ≃ₗᵢ[ℝ] ℂ}
  {G : ℂ → ℂ} {S : MonotoneStrip} {cutoff : ℝ}

/-- Positive width supplies an actual active point at the tested height. No extra
active-height witness or positive-width continuation past the point is an input. -/
theorem MatchesParentBanks.at_positive_width
    (matching : N.MatchesParentBanks positive small i D calibration G S cutoff)
    {h : ℝ} (height : h ∈ Set.Ioo 0 cutoff)
    (width : S.lower.coordinate h < S.upper.coordinate h) :
    ∀ e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots},
      K.projectedVertex e.val ∈ cuts →
      K.projectedVertex (N.spanningCompletion.parents.parent e.val) -
        K.projectedVertex e.val ∈ closedFiveSector t i →
      let frame := (fiveSectorFrame t positive small i).place
      ((∀ f j, source + frame.symm (S.lower.point h) ≠ (K.projectedTriangle f).vertex j) →
        source + frame.symm (S.lower.point h) ∈ segment ℝ (K.projectedVertex e.val)
          (K.projectedVertex (N.spanningCompletion.parents.parent e.val)) →
        G (S.lower.point h) = D.centeredCoordinatePlacement K source calibration frame
          (N.parentBankOpening D e).entranceFace (S.lower.point h)) ∧
      ((∀ f j, source + frame.symm (S.upper.point h) ≠ (K.projectedTriangle f).vertex j) →
        source + frame.symm (S.upper.point h) ∈ segment ℝ (K.projectedVertex e.val)
          (K.projectedVertex (N.spanningCompletion.parents.parent e.val)) →
        G (S.upper.point h) = D.centeredCoordinatePlacement K source calibration frame
          (N.parentBankOpening D e).exitFace (S.upper.point h)) := by
  let x := (S.lower.coordinate h + S.upper.coordinate h) / 2
  let active : ℂ := ⟨x, h - x⟩
  have active_height : active.re + active.im = h := by
    change x + (h - x) = h
    ring
  have strict : active ∈ S.strictCarrier := by
    change S.lower.coordinate (active.re + active.im) < x ∧
      x < S.upper.coordinate (active.re + active.im)
    rw [active_height]
    dsimp only [x]
    constructor <;> linarith
  exact matching active strict (by rw [active_height]; exact ⟨height.1.le, height.2.le⟩)
    h height (by rw [active_height])

end Unfoldings.ConvexCap.RadialCutForest
