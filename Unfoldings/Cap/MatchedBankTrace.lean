module

public import Unfoldings.Cap.CompletedBankTraceMatching

/-! Complete one-sided strip traces match all regular actual parent-bank pieces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  {t : ℝ} (positive : 0 < t) (small : t < 1) (i : FiveSector)
  (D : FacewiseDevelopment C N.completedRetain) (calibration : Plane ≃ₗᵢ[ℝ] ℂ)
  (G : ℂ → ℂ) (S : MonotoneStrip) (cutoff : ℝ)

/-- Match every regular bank piece up to each active strip height. Branch vertices retain
their one-sided traces; this property imposes no equality between distinct branch copies. -/
def MatchesParentBanks : Prop :=
  ∀ active ∈ S.strictCarrier, active.re + active.im ∈ Set.Icc 0 cutoff →
    ∀ h ∈ Set.Ioo 0 cutoff, h ≤ active.re + active.im →
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
            (N.parentBankOpening D e).exitFace (S.upper.point h))

theorem matchesParentBanks_of_visible_traces
    (avoids : ∀ z ∈ S.strictCarrier, z.re + z.im ∈ Set.Icc 0 cutoff →
      source + (fiveSectorFrame t positive small i).place.symm z ∉ cuts)
    (width : ∀ z ∈ S.carrier, z.re + z.im ∈ Set.Icc 0 cutoff →
      (∀ f j, source + (fiveSectorFrame t positive small i).place.symm z ≠
        (K.projectedTriangle f).vertex j) →
      ∀ k ∈ Set.Icc (z.re + z.im) cutoff,
        S.lower.coordinate k < S.upper.coordinate k →
        S.lower.coordinate (z.re + z.im) < S.upper.coordinate (z.re + z.im))
    (traces : ∀ active ∈ S.strictCarrier, active.re + active.im ∈ Set.Icc 0 cutoff →
      ∀ h ∈ Set.Icc 0 (active.re + active.im),
        D.TraceVisibleAt K source calibration (fiveSectorFrame t positive small i).place
          G {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} (S.lower.point h) ∧
        D.TraceVisibleAt K source calibration (fiveSectorFrame t positive small i).place
          G {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} (S.upper.point h)) :
    N.MatchesParentBanks positive small i D calibration G S cutoff := by
  intro active strict slab h within before e on_cut direction
  have positive_width : S.lower.coordinate (active.re + active.im) <
      S.upper.coordinate (active.re + active.im) := strict.1.trans strict.2
  have bank_traces := traces active strict slab h ⟨within.1.le, before⟩
  have first_member : S.lower.point h ∈ S.carrier := by
    change S.lower.coordinate ((S.lower.point h).re + (S.lower.point h).im) ≤
      (S.lower.point h).re ∧ (S.lower.point h).re ≤
      S.upper.coordinate ((S.lower.point h).re + (S.lower.point h).im)
    rw [S.lower.point_height]
    exact ⟨le_rfl, S.ordered h⟩
  have last_member : S.upper.point h ∈ S.carrier := by
    change S.lower.coordinate ((S.upper.point h).re + (S.upper.point h).im) ≤
      (S.upper.point h).re ∧ (S.upper.point h).re ≤
      S.upper.coordinate ((S.upper.point h).re + (S.upper.point h).im)
    rw [S.upper.point_height]
    exact ⟨S.ordered h, le_rfl⟩
  constructor
  · intro regular member
    have hslab : (S.lower.point h).re + (S.lower.point h).im ∈ Set.Icc 0 cutoff := by
      rw [S.lower.point_height]
      exact ⟨within.1.le, within.2.le⟩
    have later : active.re + active.im ∈
        Set.Icc ((S.lower.point h).re + (S.lower.point h).im) cutoff := by
      rw [S.lower.point_height]
      exact ⟨before, slab.2⟩
    have bank_width := width _ first_member hslab regular _ later positive_width
    apply N.trace_lower_parent_cut_eq_entrance positive small i e direction D calibration
      bank_traces.1 S cutoff (fun _ member => member.1) on_cut avoids member regular
    · rwa [S.lower.point_height]
    · rw [S.lower.point_height]
      rfl
    · exact bank_width
  · intro regular member
    have hslab : (S.upper.point h).re + (S.upper.point h).im ∈ Set.Icc 0 cutoff := by
      rw [S.upper.point_height]
      exact ⟨within.1.le, within.2.le⟩
    have later : active.re + active.im ∈
        Set.Icc ((S.upper.point h).re + (S.upper.point h).im) cutoff := by
      rw [S.upper.point_height]
      exact ⟨before, slab.2⟩
    have bank_width := width _ last_member hslab regular _ later positive_width
    apply N.trace_upper_parent_cut_eq_exit positive small i e direction D calibration
      bank_traces.2 S cutoff (fun _ member => member.1) on_cut avoids member regular
    · rwa [S.upper.point_height]
    · rw [S.upper.point_height]
      rfl
    · exact bank_width

end Unfoldings.ConvexCap.RadialCutForest
