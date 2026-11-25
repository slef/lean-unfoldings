module

public import Unfoldings.FewestNets.SingleCellCharge
public import Unfoldings.Geometry.CyclicSignChanges
public import Unfoldings.Geometry.MinorArcBoundaryCount

/-! A unique central crossing pairs the exact signed charges of a Gaussian cycle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.SingleCellCharge

variable {m : ℕ}

/-- The contribution of one cyclic Gaussian polygon with two marked sides. -/
def cycleCharge (label : Fin (m + 1) → Bool) (first second : Fin (m + 1)) : ℝ := by
  classical
  let side (i : Fin (m + 1)) := (label i, label (finRotate (m + 1) i))
  exact charge (∑ i, crossing (side i)) (side first) (side second) (decide (∀ i, label i = true))

private theorem cycleCharge_const (label : Bool) (first second : Fin (m + 1)) :
    cycleCharge (fun _ => label) first second = 0 := by
  cases label <;> norm_num [cycleCharge, crossing, charge, endpoints]

private theorem crossing_decided_sign (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    crossing (decide (0 < a), decide (0 < b)) = if a * b < 0 then (1 : ℝ) else 0 := by
  rcases lt_or_gt_of_ne ha with an | ap <;> rcases lt_or_gt_of_ne hb with bn | bp
  · simp [crossing, an.not_gt, bn.not_gt, (mul_pos_of_neg_of_neg an bn).not_gt]
  · simp [crossing, an.not_gt, bp, mul_neg_of_neg_of_pos an bp]
  · simp [crossing, ap, bn.not_gt, mul_neg_of_pos_of_neg ap bn]
  · simp [crossing, ap, bp, (mul_pos ap bp).not_gt]

private theorem crossing_negated (a b : Bool) : crossing (!a, !b) = crossing (a, b) := by
  cases a <;> cases b <;> rfl

/-- Opposite memberships across one plane have cancelling charges when their
true cyclic boundary has at most two changes. -/
theorem cycleCharge_complement_of_sign_changes_le_two (value : Fin (m + 1) → ℝ)
    (nonzero : ∀ i, value i ≠ 0)
    (bound : Fintype.card {i : Fin (m + 1) // value i * value (finRotate (m + 1) i) < 0} ≤ 2)
    (first second : Fin (m + 1)) :
    cycleCharge (fun i => decide (0 < value i)) first second +
      cycleCharge (fun i => !decide (0 < value i)) first second = 0 := by
  classical
  by_cases positive : ∃ i, 0 < value i
  · by_cases negative : ∃ i, value i < 0
    · have card := card_cyclic_sign_changes_eq_two value nonzero positive negative bound
      have changes : (∑ i, crossing (decide (0 < value i),
          decide (0 < value (finRotate (m + 1) i)))) = 2 := by
        simp only [crossing_decided_sign _ _ (nonzero _) (nonzero _)]
        have count : (∑ i, if value i * value (finRotate (m + 1) i) < 0 then (1 : ℕ) else 0) = 2 :=
          (Finset.sum_boole _ _).trans (by simpa only [Fintype.card_subtype, Nat.cast_id] using card)
        exact_mod_cast count
      have mixed : ¬ ∀ i, decide (0 < value i) = true := by
        intro all
        obtain ⟨i, hi⟩ := negative
        exact hi.not_gt (of_decide_eq_true (all i))
      have mixed_other : ¬ ∀ i, (!decide (0 < value i)) = true := by
        intro all
        obtain ⟨i, hi⟩ := positive
        simpa only [decide_eq_true hi, Bool.not_true, Bool.false_eq_true] using all i
      simp only [cycleCharge, crossing_negated, changes, decide_eq_false mixed, decide_eq_false mixed_other]
      exact charge_complement _ _ _ _
    · have yes (i : Fin (m + 1)) : 0 < value i :=
        lt_of_le_of_ne (le_of_not_gt (fun hi => negative ⟨i, hi⟩)) (nonzero i).symm
      simp only [decide_eq_true (yes _), Bool.not_true, cycleCharge_const, add_zero]
  · have no (i : Fin (m + 1)) : ¬ 0 < value i := fun hi => positive ⟨i, hi⟩
    simp only [decide_eq_false (no _), Bool.not_false, cycleCharge_const, add_zero]

/-- Boundary witnesses on one transverse minor arc allow at most two
sign-changing sides. Disjoint open polygon sides give distinct witnesses. -/
theorem card_sign_changes_le_two_of_boundary_witnesses {I : Type*}
    (vertices : Fin (m + 1) → Space) (value : Fin (m + 1) → ℝ)
    (disjoint : Pairwise fun i j => Disjoint
      (openMinorArc (vertices i) (vertices (finRotate (m + 1) i)))
      (openMinorArc (vertices j) (vertices (finRotate (m + 1) j))))
    {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (not_antipodal : u + v ≠ 0)
    (f : I → Space →ₗ[ℝ] ℝ) (transverse : ∀ i, f i u ≠ 0 ∨ f i v ≠ 0)
    (witness : ∀ i, value i * value (finRotate (m + 1) i) < 0 →
      ∃ x ∈ openMinorArc (vertices i) (vertices (finRotate (m + 1) i)),
        x ∈ openMinorArc u v ∧ (∀ j, 0 ≤ f j x) ∧ ∃ j, f j x = 0) :
    Fintype.card {i : Fin (m + 1) // value i * value (finRotate (m + 1) i) < 0} ≤ 2 := by
  classical
  let changed := {i : Fin (m + 1) // value i * value (finRotate (m + 1) i) < 0}
  let hits := openMinorArc u v ∩ {x | (∀ j, 0 ≤ f j x) ∧ ∃ j, f j x = 0}
  have exists_hit (i : changed) :
      ∃ x : hits, x.val ∈ openMinorArc (vertices i.val) (vertices (finRotate (m + 1) i.val)) := by
    obtain ⟨x, on_side, on_template⟩ := witness i.val i.property
    exact ⟨⟨x, on_template⟩, on_side⟩
  choose crossing hit using exists_hit
  have injective : Function.Injective crossing := by
    intro i j equal
    apply Subtype.ext
    by_contra distinct
    exact Set.disjoint_left.mp (disjoint distinct) (hit i) (equal.symm ▸ hit j)
  have below := (ENat.card_le_card_of_injective injective).trans
    (encard_openMinorArc_support_boundary_le hu hv not_antipodal f transverse)
  rw [ENat.card_eq_coe_fintype_card] at below
  exact_mod_cast below

end Unfoldings.FewestNets.SingleCellCharge
