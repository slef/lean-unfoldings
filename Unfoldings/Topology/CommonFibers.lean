module

public import Mathlib.Topology.Homeomorph.Lemmas

/-! Two compact quotient maps with exactly the same fibers identify their targets. -/

@[expose] public section

noncomputable section

namespace Unfoldings

def homeomorphOfCompactCommonFibers {A X Y : Type*}
    [TopologicalSpace A] [CompactSpace A] [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y]
    (f : A → X) (g : A → Y) (continuous_f : Continuous f) (continuous_g : Continuous g)
    (onto_f : Function.Surjective f) (onto_g : Function.Surjective g)
    (fibers : ∀ a b, f a = f b ↔ g a = g b) : X ≃ₜ Y := by
  let F (x : X) := g (Function.surjInv onto_f x)
  have agrees (a : A) : F (f a) = g a :=
    (fibers _ a).mp (Function.surjInv_eq onto_f (f a))
  have injective : Function.Injective F := by
    intro x y equal
    have equal_f := (fibers _ _).mpr equal
    simpa only [Function.surjInv_eq] using equal_f
  have surjective : Function.Surjective F := by
    intro y
    obtain ⟨a, rfl⟩ := onto_g y
    exact ⟨f a, agrees a⟩
  let e := Equiv.ofBijective F ⟨injective, surjective⟩
  have continuous_F : Continuous F := by
    apply (Topology.IsQuotientMap.of_surjective_continuous onto_f continuous_f).continuous_iff.mpr
    simpa only [Function.comp_def, agrees] using continuous_g
  have continuous_inverse : Continuous e.symm := by
    apply (Topology.IsQuotientMap.of_surjective_continuous onto_g continuous_g).continuous_iff.mpr
    have inverse_agrees (a : A) : e.symm (g a) = f a := by
      apply e.injective
      exact (e.apply_symm_apply (g a)).trans (agrees a).symm
    simpa only [Function.comp_def, inverse_agrees] using continuous_f
  exact ⟨e, continuous_F, continuous_inverse⟩

theorem homeomorphOfCompactCommonFibers_apply {A X Y : Type*}
    [TopologicalSpace A] [CompactSpace A] [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y]
    (f : A → X) (g : A → Y) (continuous_f : Continuous f) (continuous_g : Continuous g)
    (onto_f : Function.Surjective f) (onto_g : Function.Surjective g)
    (fibers : ∀ a b, f a = f b ↔ g a = g b) (a : A) :
    homeomorphOfCompactCommonFibers f g continuous_f continuous_g onto_f onto_g fibers (f a) =
      g a := by
  change g (Function.surjInv onto_f (f a)) = g a
  exact (fibers _ a).mp (Function.surjInv_eq onto_f (f a))

end Unfoldings
