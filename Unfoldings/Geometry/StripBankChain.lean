module

public import Unfoldings.Geometry.SubdivisionWallContacts

/-! Permanently collapsed cells identify every physical wall of a finite strip chain. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable {n : ℕ} (cells : Fin (n + 1) → MonotoneStrip)
  (adjacent : ∀ j : Fin n, (cells j.castSucc).upper = (cells j.succ).lower)

include adjacent

/-- Only cells strictly before the final lower bank must have collapsed. -/
theorem lower_coordinates_eq_between {h : ℝ} (a b : Fin (n + 1)) (ordered : a ≤ b)
    (collapsed : ∀ j, a ≤ j → j < b →
      (cells j).lower.coordinate h = (cells j).upper.coordinate h) :
    (cells a).lower.coordinate h = (cells b).lower.coordinate h := by
  revert ordered collapsed
  induction b using Fin.induction with
  | zero =>
    intro ordered _
    have zero : a = 0 := by
      apply Fin.ext
      change a.val = 0
      change a.val ≤ 0 at ordered
      omega
    rw [zero]
  | succ b ih =>
    intro ordered collapsed
    by_cases same : a = b.succ
    · rw [same]
    have before : a ≤ b.castSucc := by
      change a.val ≤ b.val
      have different : a.val ≠ b.val + 1 := fun equal => same (Fin.ext equal)
      change a.val ≤ b.val + 1 at ordered
      omega
    have previous := ih before (fun j first last =>
      collapsed j first (last.trans_le (Fin.castSucc_le_succ b)))
    exact previous.trans ((collapsed b.castSucc before (Nat.lt_succ_self b.val)).trans
      (congrArg (fun G : MonotoneHeightGraph => G.coordinate h) (adjacent b)))

/-- For upper banks, the first cell may remain open; all later cells collapse. -/
theorem upper_coordinates_eq_between {h : ℝ} (a b : Fin (n + 1)) (ordered : a ≤ b)
    (collapsed : ∀ j, a < j → j ≤ b →
      (cells j).lower.coordinate h = (cells j).upper.coordinate h) :
    (cells a).upper.coordinate h = (cells b).upper.coordinate h := by
  revert ordered collapsed
  induction b using Fin.induction with
  | zero =>
    intro ordered _
    have zero : a = 0 := by
      apply Fin.ext
      change a.val = 0
      change a.val ≤ 0 at ordered
      omega
    rw [zero]
  | succ b ih =>
    intro ordered collapsed
    by_cases same : a = b.succ
    · rw [same]
    have before : a ≤ b.castSucc := by
      change a.val ≤ b.val
      have different : a.val ≠ b.val + 1 := fun equal => same (Fin.ext equal)
      change a.val ≤ b.val + 1 at ordered
      omega
    have previous := ih before (fun j first last =>
      collapsed j first (last.trans (Fin.castSucc_le_succ b)))
    exact previous.trans
      ((congrArg (fun G : MonotoneHeightGraph => G.coordinate h) (adjacent b)).trans
        (collapsed b.succ (before.trans_lt (Nat.lt_succ_self b.val)) le_rfl))

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
