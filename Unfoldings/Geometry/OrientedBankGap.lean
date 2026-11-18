module

public import Unfoldings.Geometry.BankGapModel
public import Unfoldings.Geometry.TwoBankGapMetric

/-! Retain the constructed positive-side gap, not just its two boundary banks. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

/-- Radial bank geometry selects the actual counterclockwise gap region uniquely by construction. -/
structure OrientedBankGap {n : ℕ} (first second : PolygonalRay ℂ n) : Prop where
  first_outward : first.Outward
  first_nonzero : first.direction ≠ 0
  second_outward : second.Outward
  second_nonzero : second.direction ≠ 0
  phase : ∀ r : ℝ≥0, 0 < r →
    0 < (first.twoBankRatio second first_outward first_nonzero second_outward second_nonzero r).im
  common : second.start = first.start

namespace OrientedBankGap

variable {n : ℕ} {first second : PolygonalRay ℂ n} (G : OrientedBankGap first second)

/-- This is the specific positive-side region constructed from the actual ordered banks. -/
def region : Set ℂ :=
  first.twoBankGap second G.first_outward G.first_nonzero G.second_outward G.second_nonzero G.phase

/-- The intrinsic model retains the literal canonical region, together with its concrete cells. -/
def model : BankGapModel first second := by
  let cover := first.exists_twoBankGap_cell_cover second G.first_outward G.first_nonzero
    G.second_outward G.second_nonzero G.phase G.common
  let Cell := cover.choose
  let finite : Fintype Cell := cover.choose_spec.choose
  let cells : Cell → Set ℂ := cover.choose_spec.choose_spec.choose
  have data := cover.choose_spec.choose_spec.choose_spec
  exact {
    region := G.region
    closed := first.isClosed_twoBankGap second G.first_outward G.first_nonzero
      G.second_outward G.second_nonzero G.phase
    frontier_eq := first.frontier_twoBankGap second G.first_outward G.first_nonzero
      G.second_outward G.second_nonzero G.phase G.common
    banks_meet := first.twoBank_carriers_inter second G.first_outward G.first_nonzero
      G.second_outward G.second_nonzero G.phase G.common
    interior_nonempty := first.twoBankGap_interior_nonempty second G.first_outward G.first_nonzero
      G.second_outward G.second_nonzero G.phase
    regular_closed := first.twoBankGap_regular_closed second G.first_outward G.first_nonzero
      G.second_outward G.second_nonzero G.phase
    complete := first.twoBankGap_complete second G.first_outward G.first_nonzero
      G.second_outward G.second_nonzero G.phase G.common
    contractible := first.twoBankGap_contractible second G.first_outward G.first_nonzero
      G.second_outward G.second_nonzero G.phase G.common
    Cell := Cell
    finite := finite
    cells := cells
    cell_closed := fun i => (data.1 i).1
    cell_convex := fun i => (data.1 i).2.1
    cell_interior := fun i => (data.1 i).2.2
    cell_disjoint := data.2.1
    cover := data.2.2 }

/-- Canonical occupancy is retained literally, so original gap-corner charts apply directly. -/
@[simp] theorem model_region : G.model.region = G.region := rfl

/-- The canonical gap retains its original sector topology at both banks and at infinity. -/
def sectorHomeomorph : PolygonalPoint G.model.region ≃ₜ planarSector (Real.pi / 2) :=
  first.twoBankGapSectorHomeomorph second G.first_outward G.first_nonzero
    G.second_outward G.second_nonzero G.phase G.common

/-- Interior local Euclidean regularity is derived from the actual canonical gap. -/
theorem interior_chart (x : PolygonalPoint G.model.region) (inside : x.val ∈ interior G.region) :
    HasMetricBallChart ℂ x :=
  first.twoBankGap_interior_chart second G.first_outward G.first_nonzero G.second_outward
    G.second_nonzero G.phase x inside

end OrientedBankGap
end Unfoldings
