module

public import Unfoldings.Topology.FiniteMonotonePieces
public import Mathlib.Topology.UnitInterval

/-! Equality between ordered strictly increasing pieces can occur only at a shared endpoint. -/

@[expose] public section

namespace Unfoldings

theorem finite_strict_pieces_contact {n : ℕ} (F : Fin n → unitInterval → ℝ)
    (strict : ∀ j, StrictMono (F j))
    (jumps : ∀ j k : Fin n, k.val = j.val + 1 → F j 1 ≤ F k 0)
    (j k : Fin n) (s r : unitInterval) (before : j < k)
    (reversed : F k r ≤ F j s) :
    k.val = j.val + 1 ∧ s = 1 ∧ r = 0 ∧ F j s = F k r := by
  have ordered := finite_monotone_pieces F (fun j => (strict j).monotone) jumps
  have endpoint_first : s = 1 := by
    by_contra different
    have less : s < 1 := lt_of_le_of_ne s.property.2 different
    have later := ordered j k 1 r (Or.inl before)
    exact ((strict j less).trans_le later).not_ge reversed
  have endpoint_last : r = 0 := by
    by_contra different
    have more : (0 : unitInterval) < r :=
      lt_of_le_of_ne r.property.1 (Ne.symm different)
    have earlier := ordered j k s 0 (Or.inl before)
    exact (earlier.trans_lt (strict k more)).not_ge reversed
  have adjacent : k.val = j.val + 1 := by
    by_contra different
    have gap : j.val + 1 < k.val := by change j.val < k.val at before; omega
    let a : Fin n := ⟨j.val + 1, gap.trans k.isLt⟩
    have first := ordered j a s 0 (Or.inl (show j < a from Nat.lt_succ_self j.val))
    have last := ordered a k 1 r (Or.inl (show a < k from gap))
    exact (first.trans_lt ((strict a zero_lt_one).trans_le last)).not_ge reversed
  exact ⟨adjacent, endpoint_first, endpoint_last,
    le_antisymm (ordered j k s r (Or.inl before)) reversed⟩

end Unfoldings
