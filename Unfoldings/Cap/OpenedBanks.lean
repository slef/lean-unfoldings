module

public import Unfoldings.Cap.HeadingBanks
public import Unfoldings.Geometry.ChainConstruction

/-!
# Construct opened banks from curvature budgets

Opening by successive nonnegative angles rotates the heading of each later
edge by their cumulative sum. Matched lengths construct the actual banks.
A total opening smaller than the reserved quadrant margin proves their order.
The identification of these opening angles with a cap cut's curvature remains
an independent geometric obligation.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open PolygonalChain

variable {n : ℕ}

/-- The opening at the initial endpoint of edge `i` is included in its rotation. -/
def cumulativeOpening (curvature : Fin n → ℝ) (i : Fin n) : ℝ :=
  Fin.partialSum curvature i.succ

def openedBank (origin : ℂ) (length heading curvature : Fin n → ℝ) : PolygonalChain ℂ n :=
  ofHeadings origin length (fun i => heading i + cumulativeOpening curvature i)

/-- A complete local opening construction inside a common quadrant, with exact edge lengths. -/
def openedQuadrantBanks (origin : ℂ) (length heading curvature : Fin n → ℝ)
    (length_positive : ∀ i, 0 < length i) {δ : ℝ} (margin : 0 < δ)
    (headings : ∀ i, δ ≤ heading i ∧ heading i ≤ Real.pi / 2 - δ)
    (nonnegative : ∀ i, 0 ≤ curvature i) (budget : (∑ i, curvature i) < δ) :
    QuadrantBanks (openedBank origin length heading curvature)
      (ofHeadings origin length heading) where
  length := length
  positive_length := length_positive
  rightHeading := heading
  leftHeading i := heading i + cumulativeOpening curvature i
  right_bounds i := ⟨margin.trans_le (headings i).1, by linarith [(headings i).2]⟩
  left_bounds i := by
    have bounds := partialSum_bounds curvature nonnegative i.succ
    change 0 ≤ cumulativeOpening curvature i ∧ cumulativeOpening curvature i ≤ _ at bounds
    exact ⟨by linarith [(headings i).1], by linarith [(headings i).2]⟩
  heading_order i := le_add_of_nonneg_right (partialSum_bounds curvature nonnegative i.succ).1
  right_edge i := ofHeadings_edge _ _ _ i
  left_edge i := ofHeadings_edge _ _ _ i
  start := by simp only [openedBank, ofHeadings_start]

/-- The constructed banks cannot cross properly at any point inside their closed edges. -/
theorem openedBank_vertical_order (origin : ℂ) (length heading curvature : Fin n → ℝ)
    (length_positive : ∀ i, 0 < length i) {δ : ℝ} (margin : 0 < δ)
    (headings : ∀ i, δ ≤ heading i ∧ heading i ≤ Real.pi / 2 - δ)
    (nonnegative : ∀ i, 0 ≤ curvature i) (budget : (∑ i, curvature i) < δ)
    (i j : Fin n) (t s : unitInterval)
    (same_horizontal : ((openedBank origin length heading curvature).point i t).re =
      ((ofHeadings origin length heading).point j s).re) :
    ((ofHeadings origin length heading).point j s).im ≤
      ((openedBank origin length heading curvature).point i t).im :=
  (openedQuadrantBanks origin length heading curvature length_positive margin headings
    nonnegative budget).vertical_order i j t s same_horizontal

end Unfoldings.Cap
