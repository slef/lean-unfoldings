module

public import Unfoldings.Geometry.SubdivisionWallContacts

/-! Permanently collapsed cells identify every physical wall of a finite strip chain. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable {n : ℕ} (cells : Fin (n + 1) → MonotoneStrip)
  (adjacent : ∀ j : Fin n, (cells j.castSucc).upper = (cells j.succ).lower)

include adjacent

/-- No cells are discarded when their width vanishes. Their actual wall
coordinates identify both outside banks and every intermediate bank. -/
theorem collapsed_chain_bank_coordinates {h : ℝ}
    (collapsed : ∀ j, (cells j).lower.coordinate h = (cells j).upper.coordinate h)
    (j k : Fin (n + 1)) :
    (cells j).lower.coordinate h = (cells k).upper.coordinate h := by
  have starts (j : Fin (n + 1)) :
      (cells 0).lower.coordinate h = (cells j).lower.coordinate h := by
    induction j using Fin.induction with
    | zero => rfl
    | succ j ih =>
      exact ih.trans ((collapsed j.castSucc).trans
        (congrArg (fun G : MonotoneHeightGraph => G.coordinate h) (adjacent j)))
  exact (starts j).symm.trans ((starts k).trans (collapsed k))

theorem collapsed_chain_bank_points {h : ℝ}
    (collapsed : ∀ j, (cells j).lower.coordinate h = (cells j).upper.coordinate h)
    (j k : Fin (n + 1)) : (cells j).lower.point h = (cells k).upper.point h :=
  (cells j).lower.point_eq_of_same_coordinate (cells k).upper
    (collapsed_chain_bank_coordinates cells adjacent collapsed j k)

end Unfoldings.MonotoneStrip
