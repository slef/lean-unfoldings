module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Homotopy.Contractible

/-! Continuous descent through quotient maps, and contractibility of retracts. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]

def quotientContinuousDesc (f : A → X) (quotient : Topology.IsQuotientMap f)
    (g : C(A, Y)) (fibers : ∀ a b, f a = f b → g a = g b) : C(X, Y) := by
  let F (x : X) := g (Function.surjInv quotient.surjective x)
  have agrees (a : A) : F (f a) = g a :=
    fibers _ a (Function.surjInv_eq quotient.surjective (f a))
  refine ⟨F, quotient.continuous_iff.mpr ?_⟩
  have equal : F ∘ f = g := funext agrees
  rw [equal]
  exact g.continuous

theorem quotientContinuousDesc_apply (f : A → X) (quotient : Topology.IsQuotientMap f)
    (g : C(A, Y)) (fibers : ∀ a b, f a = f b → g a = g b) (a : A) :
    quotientContinuousDesc f quotient g fibers (f a) = g a :=
  fibers _ a (Function.surjInv_eq quotient.surjective (f a))

theorem contractible_of_retraction [ContractibleSpace X] (inclusion : C(Y, X)) (retract : C(X, Y))
    (identity : ∀ y, retract (inclusion y) = y) : ContractibleSpace Y := by
  apply (contractible_iff_id_nullhomotopic Y).mpr
  have null := ((id_nullhomotopic X).comp_left inclusion).comp_right retract
  have equal : retract.comp ((ContinuousMap.id X).comp inclusion) = ContinuousMap.id Y :=
    ContinuousMap.ext identity
  rwa [equal] at null

end Unfoldings
