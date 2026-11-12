module

public import Unfoldings.Geometry.StripBankChain

/-! Bank-chain identities need only the contacts at the height actually being compared. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

private def frozenBanks (S : MonotoneStrip) (h : ℝ) : MonotoneStrip where
  lower := MonotoneHeightGraph.constant (S.lower.coordinate h)
  upper := MonotoneHeightGraph.constant (S.upper.coordinate h)
  ordered _ := S.ordered h

variable {n : ℕ} (cells : Fin (n + 1) → MonotoneStrip) {h : ℝ}

/-- Freezing bank coordinates makes the purely algebraic chain identity
independent of how a physical wall is extended outside the tested slab. -/
theorem lower_coordinates_eq_between_of_contacts
    (contacts : ∀ j : Fin n,
      (cells j.castSucc).upper.coordinate h = (cells j.succ).lower.coordinate h)
    (a b : Fin (n + 1)) (ordered : a ≤ b)
    (collapsed : ∀ j, a ≤ j → j < b →
      (cells j).lower.coordinate h = (cells j).upper.coordinate h) :
    (cells a).lower.coordinate h = (cells b).lower.coordinate h := by
  let frozen := fun j => frozenBanks (cells j) h
  have adjacent (j : Fin n) : (frozen j.castSucc).upper = (frozen j.succ).lower :=
    congrArg MonotoneHeightGraph.constant (contacts j)
  exact lower_coordinates_eq_between frozen adjacent (h := 0) a b ordered collapsed

theorem upper_coordinates_eq_between_of_contacts
    (contacts : ∀ j : Fin n,
      (cells j.castSucc).upper.coordinate h = (cells j.succ).lower.coordinate h)
    (a b : Fin (n + 1)) (ordered : a ≤ b)
    (collapsed : ∀ j, a < j → j ≤ b →
      (cells j).lower.coordinate h = (cells j).upper.coordinate h) :
    (cells a).upper.coordinate h = (cells b).upper.coordinate h := by
  let frozen := fun j => frozenBanks (cells j) h
  have adjacent (j : Fin n) : (frozen j.castSucc).upper = (frozen j.succ).lower :=
    congrArg MonotoneHeightGraph.constant (contacts j)
  exact upper_coordinates_eq_between frozen adjacent (h := 0) a b ordered collapsed

theorem collapsed_chain_coordinates_of_contacts
    (contacts : ∀ j : Fin n,
      (cells j.castSucc).upper.coordinate h = (cells j.succ).lower.coordinate h)
    (collapsed : ∀ j, (cells j).lower.coordinate h = (cells j).upper.coordinate h)
    (a b : Fin (n + 1)) :
    (cells a).lower.coordinate h = (cells b).upper.coordinate h := by
  let frozen := fun j => frozenBanks (cells j) h
  have adjacent (j : Fin n) : (frozen j.castSucc).upper = (frozen j.succ).lower :=
    congrArg MonotoneHeightGraph.constant (contacts j)
  exact collapsed_chain_bank_coordinates frozen adjacent (h := 0) collapsed a b

theorem collapsed_chain_points_of_contacts
    (contacts : ∀ j : Fin n,
      (cells j.castSucc).upper.coordinate h = (cells j.succ).lower.coordinate h)
    (collapsed : ∀ j, (cells j).lower.coordinate h = (cells j).upper.coordinate h)
    (a b : Fin (n + 1)) : (cells a).lower.point h = (cells b).upper.point h :=
  (cells a).lower.point_eq_of_same_coordinate (cells b).upper
    (collapsed_chain_coordinates_of_contacts cells contacts collapsed a b)

end Unfoldings.MonotoneStrip
