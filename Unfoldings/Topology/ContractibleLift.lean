module

public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Covering lifts from contractible spaces

Lift a homotopy from a constant map to the given map, starting with a constant
lift. This needs no local path-connectedness hypothesis on the domain.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {A E X : Type*} [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace X]

theorem exists_covering_lift_of_contractible [ContractibleSpace A]
    (p : E → X) (covering : IsCoveringMap p) (surjective : Function.Surjective p)
    (f : C(A, X)) : ∃ F : C(A, E), p ∘ F = f := by
  have null : f.Nullhomotopic := by
    have result := (id_nullhomotopic A).comp_right f
    simpa only [ContinuousMap.comp_id] using result
  obtain ⟨c, ⟨H⟩⟩ := null
  obtain ⟨e, at_e⟩ := surjective c
  have initial : ∀ a, H.symm (0, a) = p ((ContinuousMap.const A e) a) := by
    intro a
    rw [H.symm.apply_zero]
    exact at_e.symm
  let lift := covering.liftHomotopy H.symm (ContinuousMap.const A e) initial
  let F : C(A, E) := ⟨fun a => lift (1, a),
    lift.continuous.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨F, funext (fun a => ?_)⟩
  have equal := congrFun
    (covering.liftHomotopy_lifts H.symm (ContinuousMap.const A e) initial) (1, a)
  exact equal.trans (H.symm.apply_one a)

end Unfoldings
