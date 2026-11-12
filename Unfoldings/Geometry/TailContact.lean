module

public import Unfoldings.Geometry.FiniteWaterfall

/-! Completing an actual tail is invariant under physical bank contact on its height slab. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

theorem CompletesTail.of_point_eqOn {p : ℂ} {tail G H : MonotoneHeightGraph} {cutoff : ℝ}
    (completion : CompletesTail p tail cutoff G) (nonnegative : 0 ≤ p.re + p.im)
    (active : p.re + p.im ≤ cutoff)
    (contact : Set.EqOn G.point H.point (Set.Icc 0 cutoff)) :
    CompletesTail p tail cutoff H := by
  refine ⟨?_, ?_⟩
  · exact (congrArg Complex.re (contact ⟨le_rfl, nonnegative.trans active⟩)).symm.trans
      completion.1
  · intro h height
    exact (congrArg Complex.re (contact ⟨nonnegative.trans height.1, height.2⟩)).symm.trans
      (completion.2 h height)

end Unfoldings.MonotoneStrip
