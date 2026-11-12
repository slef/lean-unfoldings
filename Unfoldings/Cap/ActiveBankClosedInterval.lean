module

public import Unfoldings.Cap.RadialStripPointOrder
public import Unfoldings.Geometry.RecoverableStripClosure

/-! A positive-width bank height lies strictly before an actual closed interval of both banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}
  (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)

/-- Local positive width supplies a later active height. Recoverable pinches then include
every earlier bank point, even at cut vertices, in the actual closed trace domain. -/
theorem exists_later_height_with_all_prior_banks_closed {h : ℝ}
    (height : h ∈ Set.Ioo 0 cutoff) (width : S.lower.coordinate h < S.upper.coordinate h) :
    ∃ b : ℝ, h < b ∧ b < cutoff ∧
      ∀ k ∈ Set.Icc 0 b, S.lower.point k ∈ closure data.strictDomain ∧
        S.upper.point k ∈ closure data.strictDomain := by
  let U := Set.Ioo (0 : ℝ) cutoff ∩ {k | S.lower.coordinate k < S.upper.coordinate k}
  have opened : IsOpen U := isOpen_Ioo.inter (isOpen_lt S.lower.continuous S.upper.continuous)
  obtain ⟨δ, positive, ball⟩ := Metric.isOpen_iff.mp opened h ⟨height, width⟩
  let b := h + δ / 2
  have after : h < b := by dsimp only [b]; linarith
  have close : b ∈ Metric.ball h δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr after.le)]
    dsimp only [b]
    linarith
  have active := ball close
  have endpoint := S.bank_points_mem_closure_of_width ⟨active.1.1.le, active.1.2.le⟩ active.2
  refine ⟨b, after, active.1.2, ?_⟩
  intro k bounds
  have lower_member : S.lower.point k ∈ S.carrier := by
    change S.lower.coordinate ((S.lower.point k).re + (S.lower.point k).im) ≤
      (S.lower.point k).re ∧ (S.lower.point k).re ≤
        S.upper.coordinate ((S.lower.point k).re + (S.lower.point k).im)
    simp only [S.lower.point_height]
    exact ⟨le_rfl, S.ordered k⟩
  have upper_member : S.upper.point k ∈ S.carrier := by
    change S.lower.coordinate ((S.upper.point k).re + (S.upper.point k).im) ≤
      (S.upper.point k).re ∧ (S.upper.point k).re ≤
        S.upper.coordinate ((S.upper.point k).re + (S.upper.point k).im)
    simp only [S.upper.point_height]
    exact ⟨S.ordered k, le_rfl⟩
  exact ⟨data.closed_initial endpoint.1 lower_member
      (by simpa only [S.lower.point_height] using bounds),
    data.closed_initial endpoint.1 upper_member
      (by simpa only [S.lower.point_height, S.upper.point_height] using bounds)⟩

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
