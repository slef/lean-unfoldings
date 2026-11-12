module

public import Unfoldings.Geometry.StrictStripInsertion
public import Unfoldings.Geometry.MonotoneStripInsertion
public import Mathlib.Topology.Order.DenselyOrdered

/-! A permanently merged child follows the inserted actual tail after its leaf. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

/-- Every permanently collapsed positive tail follows one of the specified
actual paths, starting no earlier than that path's own leaf. -/
def TerminalTailsFrom {ι : Type*} (p : ι → ℂ) (tail : ι → MonotoneHeightGraph)
    (cutoff : ℝ) : Prop :=
  ∀ h ∈ Set.Ioo (0 : ℝ) cutoff,
    (∀ k ∈ Set.Icc h cutoff, S.lower.coordinate k = S.upper.coordinate k) →
    ∃ j, (p j).re + (p j).im ≤ h ∧ ∀ k ∈ Set.Icc h cutoff,
      S.lower.coordinate k = (tail j).coordinate k ∧
        S.upper.coordinate k = (tail j).coordinate k

/-- A positive-width target prevents either new child from terminating before
the target. Inserting the source itself needs no positive-width condition. -/
theorem insertionGraph_terminal_tail (p : ℂ) (member : p ∈ S.carrier)
    (tail : MonotoneHeightGraph) (at_target : tail.coordinate (p.re + p.im) = p.re)
    {cutoff : ℝ} (below : p.re + p.im ≤ cutoff)
    (first : S.lower.StrictCoordinatesOn (Set.Icc 0 cutoff))
    (last : S.upper.StrictCoordinatesOn (Set.Icc 0 cutoff))
    (target_width : p.re + p.im = 0 ∨
      S.lower.coordinate (p.re + p.im) < S.upper.coordinate (p.re + p.im))
    (trapped : ∀ k ∈ Set.Icc (p.re + p.im) cutoff,
      S.lower.coordinate k ≤ tail.coordinate k ∧ tail.coordinate k ≤ S.upper.coordinate k) :
    let G := S.insertionGraph p member tail at_target
    let bounds := S.insertionGraph_bounds p member tail at_target
    ∀ child ∈ ({S.lowerSplit G bounds, S.upperSplit G bounds} : Set MonotoneStrip),
      ∀ h ∈ Set.Ioo (0 : ℝ) cutoff,
        (∀ k ∈ Set.Icc h cutoff, child.lower.coordinate k = child.upper.coordinate k) →
        p.re + p.im ≤ h ∧ ∀ k ∈ Set.Icc h cutoff,
          child.lower.coordinate k = tail.coordinate k ∧
            child.upper.coordinate k = tail.coordinate k := by
  let G := S.insertionGraph p member tail at_target
  let bounds := S.insertionGraph_bounds p member tail at_target
  refine fun child child_mem h height merged => ?_
  have after : p.re + p.im ≤ h := by
    by_contra not_after
    have before : h < p.re + p.im := lt_of_not_ge not_after
    have width : S.lower.coordinate (p.re + p.im) < S.upper.coordinate (p.re + p.im) :=
      target_width.resolve_left (fun equal => by linarith [height.1])
    have closure_point : p.re + p.im ∈ closure (Set.Ioo h (p.re + p.im)) := by
      rw [closure_Ioo before.ne]
      exact ⟨before.le, le_rfl⟩
    have opened : IsOpen {k | S.lower.coordinate k < S.upper.coordinate k} :=
      isOpen_lt S.lower.continuous S.upper.continuous
    obtain ⟨k, positive_width, within⟩ := mem_closure_iff_nhds.mp closure_point _
      (opened.mem_nhds width)
    have strict := S.interiorConnector_strict_before_target member
      (first.mono (Set.Icc_subset_Icc_right below))
      (last.mono (Set.Icc_subset_Icc_right below))
      (height.1.le.trans within.1.le) within.2 positive_width
    have at_k : G.coordinate k = (S.interiorConnector p).coordinate k := ite_eq_left within.2.le
    have equal := merged k ⟨within.1.le, within.2.le.trans below⟩
    rcases child_mem with rfl | rfl
    · change S.lower.coordinate k = G.coordinate k at equal
      rw [at_k] at equal
      exact strict.1.ne equal
    · change G.coordinate k = S.upper.coordinate k at equal
      rw [at_k] at equal
      exact strict.2.ne equal
  refine ⟨after, fun k within => ?_⟩
  have tail_value : G.coordinate k = tail.coordinate k :=
    S.insertionGraph_preserves_tail p member tail at_target (after.trans within.1)
      (trapped k ⟨after.trans within.1, within.2⟩).1
      (trapped k ⟨after.trans within.1, within.2⟩).2
  have equal := merged k within
  rcases child_mem with rfl | rfl
  · exact ⟨equal.trans tail_value, tail_value⟩
  · exact ⟨tail_value, equal.symm.trans tail_value⟩

theorem insertionGraph_terminalTailsFrom {ι : Type*} (p : ι → ℂ)
    (tail : ι → MonotoneHeightGraph) (j : ι) (member : p j ∈ S.carrier)
    (at_target : (tail j).coordinate ((p j).re + (p j).im) = (p j).re)
    {cutoff : ℝ} (below : (p j).re + (p j).im ≤ cutoff)
    (first : S.lower.StrictCoordinatesOn (Set.Icc 0 cutoff))
    (last : S.upper.StrictCoordinatesOn (Set.Icc 0 cutoff))
    (target_width : (p j).re + (p j).im = 0 ∨
      S.lower.coordinate ((p j).re + (p j).im) <
        S.upper.coordinate ((p j).re + (p j).im))
    (trapped : ∀ k ∈ Set.Icc ((p j).re + (p j).im) cutoff,
      S.lower.coordinate k ≤ (tail j).coordinate k ∧
        (tail j).coordinate k ≤ S.upper.coordinate k) :
    let G := S.insertionGraph (p j) member (tail j) at_target
    let bounds := S.insertionGraph_bounds (p j) member (tail j) at_target
    (S.lowerSplit G bounds).TerminalTailsFrom p tail cutoff ∧
      (S.upperSplit G bounds).TerminalTailsFrom p tail cutoff := by
  have good := S.insertionGraph_terminal_tail (p j) member (tail j) at_target below
    first last target_width trapped
  constructor
  · intro h height merged
    exact ⟨j, good _ (Or.inl rfl) h height merged⟩
  · intro h height merged
    exact ⟨j, good _ (Or.inr rfl) h height merged⟩

end Unfoldings.MonotoneStrip
