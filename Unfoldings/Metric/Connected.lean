module

public import Unfoldings.Metric.FiniteComponent
public import Mathlib.Topology.Connected.Clopen

/-! A preconnected extended metric space has finite distances. -/

@[expose] public section

namespace Unfoldings

variable {X : Type*} [EMetricSpace X] [PreconnectedSpace X]

theorem finiteComponent_eq_univ (p : X) : finiteComponent p = Set.univ :=
  IsClopen.eq_univ ⟨isClosed_finiteComponent p, isOpen_finiteComponent p⟩
    ⟨p, by simp [finiteComponent]⟩

theorem edist_ne_top_of_preconnected (x y : X) : edist x y ≠ ⊤ := by
  have member : x ∈ finiteComponent y := (finiteComponent_eq_univ y).ge (Set.mem_univ x)
  exact member

end Unfoldings
