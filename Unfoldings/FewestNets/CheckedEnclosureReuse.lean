module

public import Unfoldings.FewestNets.CheckedReal

/-! Kernel-validated cached intervals for repeated coordinate tests. -/

@[expose] public section

namespace Unfoldings.FewestNets.CheckedReal

variable {D : ℕ} {x : ℝ}

/-- A supplied interval contains the entire computed enclosure. -/
def insideBounds (a : CheckedReal D x) (interval : FixedPointInterval D) : Bool :=
  a.bounds.any fun i => decide (interval.lo ≤ i.lo ∧ i.hi ≤ interval.hi)

/-- Reuse a validated wider interval in repeated downstream computations. -/
def withWiderBounds (a : CheckedReal D x) (interval : FixedPointInterval D)
    (valid : a.insideBounds interval = true) : CheckedReal D x where
  bounds := some interval
  sound j hj := by
    cases ha : a.bounds with
    | none => simp [insideBounds, ha] at valid
    | some i =>
      have ordered : interval.lo ≤ i.lo ∧ i.hi ≤ interval.hi := by
        simpa [insideBounds, ha] using valid
      have contained := a.sound i ha
      have eq := Option.some.inj hj
      subst j
      exact ⟨(by exact_mod_cast ordered.1 : (interval.lo : ℝ) ≤ i.lo).trans contained.1,
        contained.2.trans (by exact_mod_cast ordered.2)⟩

end Unfoldings.FewestNets.CheckedReal
