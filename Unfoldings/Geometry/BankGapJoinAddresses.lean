module

public import Unfoldings.Geometry.BankGapAddressUniqueness

/-! The actual gap rim point has exactly the two addresses adjacent to its named join. -/

@[expose] public section

open scoped NNReal

namespace Unfoldings.BankGapModel

variable {n : ℕ} {first second : PolygonalRay ℂ (n + 1)}
  (M : BankGapModel first second) (G : OrientedBankGap first second)

include G in
/-- At the tail join the original side is unique, and the two literal addresses are the
last finite edge at time one and the tail at time zero. -/
theorem addressFrontier_eq_tail_zero
    (genuine : ∀ side i, (M.bank side).chain.edge i ≠ 0) (side other : Bool)
    (a : PolygonalRay.Address (n + 1))
    (equal : M.addressFrontier other a = M.addressFrontier side (.inr 0)) :
    other = side ∧ (a = .inr 0 ∨ a = .inl (Fin.last n, 1)) := by
  let R := M.bank side
  have outward := M.bank_outward G side
  have nonzero := M.bank_direction_ne_zero G side
  have away : R.tail 0 ≠ R.start := by
    intro eq
    have genuine_last : R.chain.vertex (Fin.last n).castSucc ≠
        R.chain.vertex (Fin.last n).succ :=
      fun h => genuine side _ (sub_eq_zero.mpr h.symm)
    have radial := R.inner_terminal_edge_pos outward (Fin.last n) genuine_last
    have finish : R.chain.vertex (Fin.last n).succ = R.start := R.tail_zero.symm.trans eq
    rw [finish, sub_self, inner_zero_left] at radial
    exact lt_irrefl _ radial
  have same := M.side_eq_of_address_eq G side other (.inr 0) a away equal.symm
  subst other
  refine ⟨rfl, ?_⟩
  have positions : R.addressPoint a = R.tail 0 := congrArg Subtype.val equal
  cases a with
  | inl b =>
    rcases b with ⟨i, t⟩
    have last : R.chain.point i t = R.chain.vertex (Fin.last (n + 1)) :=
      positions.trans R.tail_zero
    obtain ⟨hi, ht⟩ := PolygonalChain.RadialFrom.point_eq_last R.chain outward.1 (genuine side)
      i t last
    exact Or.inr (congrArg Sum.inl (Prod.ext (Fin.succ_injective _ hi) ht))
  | inr t =>
    exact Or.inl (congrArg Sum.inr ((R.tail_radius_strictMono outward nonzero).injective
      (congrArg (dist R.start) positions)))

end Unfoldings.BankGapModel
