module

public import Unfoldings.Cap.StripCircleBanks

/-! Closed circle sections retain both actual banks and allow a collapsed pinch section. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

/-- Both actual approached bank points, including a section consisting of one pinch point. -/
structure ClosedBankCircleSection (G : ℂ → ℂ) (center : ℂ) (cutoff radius : ℝ) where
  lowerHeight : ℝ
  upperHeight : ℝ
  lower_bounds : lowerHeight ∈ Set.Icc 0 cutoff
  upper_bounds : upperHeight ∈ Set.Icc 0 cutoff
  lower_closed : S.lower.point lowerHeight ∈ closure
    {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff}
  upper_closed : S.upper.point upperHeight ∈ closure
    {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff}
  lower_radius : ‖G (S.lower.point lowerHeight) - center‖ = radius
  upper_radius : ‖G (S.upper.point upperHeight) - center‖ = radius

namespace BankCircleSlice

variable {S} {G : ℂ → ℂ} {center : ℂ} {cutoff radius : ℝ}

def toClosedSection (slice : S.BankCircleSlice G center cutoff radius) :
    S.ClosedBankCircleSection G center cutoff radius where
  lowerHeight := slice.lowerHeight
  upperHeight := slice.upperHeight
  lower_bounds := slice.lower_bounds
  upper_bounds := slice.upper_bounds
  lower_closed := slice.lower_closed
  upper_closed := slice.upper_closed
  lower_radius := slice.lower_radius
  upper_radius := slice.upper_radius

end BankCircleSlice
end Unfoldings.MonotoneStrip
