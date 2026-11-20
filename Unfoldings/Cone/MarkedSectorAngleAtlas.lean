module

public import Unfoldings.Cone.MarkedSectorBankStack

/-! Assemble a cyclic atlas from positive local sector angles summing to a full turn. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing.BankStackCyclicClass

variable {G Edge : Type*} {Parameter : Edge → Type*}
  (X : Option G → Type*) [∀ i, EMetricSpace (X i)] (stack : Edge → List G)
  (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))
  {n : ℕ} (H : BankStackCyclicClass X stack base gap n)

local notation "EndAt" => bankStackEndpoint stack X base gap
local notation "Prev[" j "]" => Equiv.symm (finRotate (n + 1)) j
local notation "Curve" => bankStackLeftCurve stack X base gap

/-- A full turn of calibrated marked sectors gives an atlas in their original cyclic order. -/
def MarkedAtlas.ofGerms [Nontrivial (Fin (n + 1))]
    (angle : Fin (n + 1) → ℝ) (full : (∑ i, angle i) = 2 * Real.pi)
    (parameterize : ∀ i, unitInterval ≃ Parameter (H.time i).1.1)
    (at_zero : ∀ i, parameterize i 0 = (H.time i).2)
    (length : Fin (n + 1) → ℝ) (length_pos : ∀ i, 0 < length i)
    (metric : ∀ i (t : unitInterval),
      edist (Curve (H.time i).1 (parameterize i 0)) (Curve (H.time i).1 (parameterize i t)) =
        ENNReal.ofReal (t.val * length i))
    (reflected : Fin (n + 1) → Bool)
    (sectors : ∀ i, ∃ mark : Bool → unitInterval → X (H.center i).1,
      Nonempty (MarkedSectorGerm (H.center i).2 (angle i) mark
        (fun b => if b = reflected i then length (Prev[i]) else length i)) ∧
      (∀ t, EndAt (H.side i) (H.time i).1 (parameterize i t) =
        ⟨(H.center i).1, mark (!(reflected i)) t⟩) ∧
      ∀ t, EndAt (!(H.side (Prev[i]))) (H.time (Prev[i])).1 (parameterize (Prev[i]) t) =
        ⟨(H.center i).1, mark (reflected i) t⟩) :
    MarkedAtlas X stack base gap H := by
  classical
  choose mark chart before after using sectors
  let heading : Fin (n + 2) → ℝ := Fin.partialSum angle
  have difference (i : Fin (n + 1)) : heading i.succ - heading i.castSucc = angle i := by
    change Fin.partialSum angle i.succ - _ = _
    rw [Fin.partialSum_succ]
    ring
  have pos (i : Fin (n + 1)) : 0 < angle i := (Classical.choice (chart i)).sector.angle_pos
  have increasing : StrictMono heading := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    apply sub_pos.mp
    rw [difference]
    exact pos i
  have finish : heading (Fin.last (n + 1)) = 2 * Real.pi := by
    suffices heading (Fin.last (n + 1)) = ∑ i, angle i from this.trans full
    change ((List.ofFn angle).take (n + 1)).sum = _
    rw [List.take_of_length_le (by simp)]
    exact List.sum_ofFn
  have width (i : Fin (n + 1)) : heading i.succ - heading i.castSucc < 2 * Real.pi := by
    rw [difference]
    obtain ⟨j, different⟩ := exists_ne i
    have positive : 0 < ∑ k ∈ Finset.univ.erase i, angle k :=
      Finset.sum_pos (fun k _ => pos k) ⟨j, Finset.mem_erase.mpr ⟨different, Finset.mem_univ _⟩⟩
    have total := (Finset.sum_erase_add _ angle (Finset.mem_univ i)).trans full
    linarith
  exact {
    heading := heading
    ordered := increasing
    start := Fin.partialSum_zero angle
    finish := finish
    width := width
    parameterize := parameterize
    at_zero := at_zero
    length := length
    length_pos := length_pos
    metric := metric
    reflected := reflected
    mark := mark
    before := before
    after := fun i t => by
      have h := after (finRotate (n + 1) i) t
      rw [(finRotate (n + 1)).symm_apply_apply] at h
      exact h
    germ := fun i => (difference i).symm ▸ Classical.choice (chart i)
  }

end Unfoldings.MetricGluing.BankStackCyclicClass
