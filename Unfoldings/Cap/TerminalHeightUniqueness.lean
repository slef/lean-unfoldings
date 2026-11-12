module

public import Unfoldings.Cap.ClosedRadialBankTrace
public import Unfoldings.Cap.EmptyCircleContinuation

/-! An approached permanent terminal has a unique physical height, independent of circle radius. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MonotoneStrip

/-- A permanently merged tail has no approached strict bank above its first merged height. -/
theorem approached_bank_height_le_merged_height (S : MonotoneStrip)
    (H : MonotoneHeightGraph) {h a cutoff : ℝ}
    (closed : H.point h ∈ closure
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff})
    (merged : ∀ k ∈ Set.Icc a cutoff, S.lower.coordinate k = S.upper.coordinate k) : h ≤ a := by
  by_contra before
  obtain ⟨z, strict, bounds, above⟩ :=
    active_above_of_bank_mem_closure H closed (lt_of_not_ge before)
  have width := strict.1.trans strict.2
  rw [merged _ ⟨above.le, bounds.2⟩] at width
  exact lt_irrefl _ width

end Unfoldings.MonotoneStrip

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  {B : N.FiveSectorFrameData positive small (N.completedDevelopment D)}
  {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}
  {data : N.RadialStripTraceData positive small D
    (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff}

/-- Reconstructing comparison arcs at another radius preserves the terminal height. -/
theorem EmptyCircleContinuation.height_eq
    {physicalRadius radius otherPhysicalRadius otherRadius : ℝ}
    (first : B.EmptyCircleContinuation i data physicalRadius radius)
    (last : B.EmptyCircleContinuation i data otherPhysicalRadius otherRadius) :
    first.height = last.height := by
  have included : S.openSlab 0 cutoff ⊆ data.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  exact le_antisymm
    (S.approached_bank_height_le_merged_height S.lower
      (closure_mono included first.lower_closed) last.merged)
    (S.approached_bank_height_le_merged_height S.lower
      (closure_mono included last.lower_closed) first.merged)

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
