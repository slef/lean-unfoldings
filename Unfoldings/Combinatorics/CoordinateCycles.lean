module

public import Unfoldings.Combinatorics.GraphCycleRank
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Algebra.Module.Submodule.Equiv

/-! Coordinate cycles and their restriction to selected edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Module
open scoped BigOperators

variable {V E : Type*} [Fintype E] {K : Type*} [Field K]

/-- A coordinate edge chain pairs with edge potentials by a finite sum. -/
def chainPairing : (E → K) →ₗ[K] Module.Dual K (E → K) :=
  ∑ e : E, LinearMap.smulRight (LinearMap.proj e) (LinearMap.proj e)

@[simp] theorem chainPairing_apply (x y : E → K) :
    chainPairing x y = ∑ e, x e * y e := by
  simp [chainPairing, LinearMap.sum_apply, LinearMap.smulRight_apply, smul_eq_mul]

/-- Every linear functional on the finite edge-potential space has unique coordinates. -/
def chainPairingEquiv : (E → K) ≃ₗ[K] Module.Dual K (E → K) := by
  classical
  have injective : Function.Injective (chainPairing (E := E) (K := K)) := by
    intro x y h
    funext e
    have eval := congrArg (fun t : Module.Dual K (E → K) => t (Pi.single e 1)) h
    simpa [chainPairing_apply, Pi.single_apply, mul_ite] using eval
  exact LinearEquiv.ofInjectiveOfFinrankEq chainPairing injective Subspace.dual_finrank_eq.symm

@[simp] theorem chainPairingEquiv_apply (x y : E → K) :
    chainPairingEquiv x y = ∑ e, x e * y e := chainPairing_apply x y

variable (source target : E → V)

/-- An edge chain is a cycle when every vertex potential has zero pairing with it
after taking differences across the edges. -/
def coordinateCycleSpace : Submodule K (E → K) :=
  (edgeCycleSpace source target K).comap (chainPairing (E := E) (K := K))

theorem mem_coordinateCycleSpace (x : E → K) :
    x ∈ coordinateCycleSpace source target ↔
      ∀ f : V → K, ∑ e, x e * (f (target e) - f (source e)) = 0 := by
  change chainPairing x ∈ LinearMap.ker (edgeCoboundary source target K).dualMap ↔ _
  rw [LinearMap.mem_ker]
  constructor
  · intro zero f
    have h := congrArg (fun z : Module.Dual K (V → K) => z f) zero
    simpa [LinearMap.dualMap_apply, chainPairing_apply] using h
  · intro zero
    ext f
    simpa [LinearMap.dualMap_apply, chainPairing_apply] using zero f

theorem finrank_coordinateCycleSpace_add_card_vertex [Fintype V] :
    finrank K (coordinateCycleSpace (K := K) source target) + Fintype.card V =
      Fintype.card E + Nat.card (endpointGraph source target).ConnectedComponent := by
  have rank := finrank_edgeCycleSpace_add_card_vertex source target K
  let equivalence := chainPairingEquiv (E := E) (K := K)
  have surjective : LinearMap.range equivalence.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr equivalence.surjective
  have eq : finrank K (coordinateCycleSpace (K := K) source target) =
      finrank K (edgeCycleSpace source target K) :=
    (Submodule.comap_equiv_self_of_inj_of_le equivalence.injective
      (show edgeCycleSpace source target K ≤ LinearMap.range equivalence.toLinearMap from
        surjective ▸ le_top)).finrank_eq
  rwa [eq]

variable (selected : E → Prop)

/-- Chains on the selected edges are extended with value zero on every other edge. -/
def extendChain [DecidablePred selected] :
    ({e // selected e} → K) →ₗ[K] (E → K) where
  toFun x e := if h : selected e then x ⟨e, h⟩ else 0
  map_add' x y := by
    funext e
    by_cases h : selected e <;> simp [h]
  map_smul' k x := by
    funext e
    by_cases h : selected e <;> simp [h]

omit [Fintype E] in
@[simp] theorem extendChain_apply_of_mem [DecidablePred selected] (x : {e // selected e} → K)
    (e : E) (h : selected e) : extendChain selected x e = x ⟨e, h⟩ := dite_eq_left h

omit [Fintype E] in
@[simp] theorem extendChain_apply_of_not_mem [DecidablePred selected] (x : {e // selected e} → K)
    (e : E) (h : ¬ selected e) : extendChain selected x e = 0 := dite_eq_right h

/-- Extending by zero preserves the cycle condition. -/
theorem extendChain_mem_coordinateCycleSpace_iff [DecidablePred selected]
    (x : {e // selected e} → K) :
    extendChain selected x ∈ coordinateCycleSpace source target ↔
      x ∈ coordinateCycleSpace (source ∘ Subtype.val) (target ∘ Subtype.val) := by
  simp only [mem_coordinateCycleSpace, Function.comp_apply]
  have pairing (f : V → K) :
      (∑ e : E, extendChain selected x e * (f (target e) - f (source e))) =
        ∑ e : {e // selected e}, x e * (f (target e.val) - f (source e.val)) := by
    calc
      _ = ∑ e ∈ Finset.univ.filter selected,
          extendChain selected x e * (f (target e) - f (source e)) := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro e _ h
        have excluded : ¬ selected e := fun he => h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
        rw [extendChain_apply_of_not_mem selected x e excluded, zero_mul]
      _ = ∑ e : {e // selected e}, x e * (f (target e.val) - f (source e.val)) := by
        rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
        apply Finset.sum_congr rfl
        intro e _
        rw [extendChain_apply_of_mem selected x e.val e.property]
  simp only [pairing]

/-- A selected-edge cycle is exactly a full cycle vanishing on excluded edges. -/
def selectedCycleEquiv [DecidablePred selected] :
    coordinateCycleSpace (K := K) (source ∘ (Subtype.val : {e // selected e} → E))
      (target ∘ Subtype.val) ≃ₗ[K]
    ↥(coordinateCycleSpace source target ⊓ LinearMap.ker
      (LinearMap.funLeft K K (Subtype.val : {e // ¬ selected e} → E))) := by
  let cycle := coordinateCycleSpace (K := K) (source ∘ (Subtype.val : {e // selected e} → E))
    (target ∘ Subtype.val)
  let excluded := LinearMap.funLeft K K (Subtype.val : {e // ¬ selected e} → E)
  let map : cycle →ₗ[K] (E → K) := (extendChain selected).comp cycle.subtype
  let supported := coordinateCycleSpace (K := K) source target ⊓ LinearMap.ker excluded
  let restricted := map.codRestrict supported (fun x =>
    ⟨(extendChain_mem_coordinateCycleSpace_iff source target selected x.val).mpr x.property,
      LinearMap.mem_ker.mpr (funext fun e =>
        extendChain_apply_of_not_mem selected x.val e e.property)⟩)
  apply LinearEquiv.ofBijective restricted
  · constructor
    · intro x y h
      apply Subtype.ext
      funext e
      have equal := congrArg (fun z : supported => z.val e.val) h
      change extendChain selected x.val e.val = extendChain selected y.val e.val at equal
      rw [extendChain_apply_of_mem selected x.val e.val e.property,
        extendChain_apply_of_mem selected y.val e.val e.property] at equal
      exact equal
    · intro y
      let x : {e // selected e} → K := y.val ∘ Subtype.val
      have ext_eq : extendChain selected x = y.val := by
        funext e
        by_cases h : selected e
        · exact extendChain_apply_of_mem selected x e h
        · rw [extendChain_apply_of_not_mem selected x e h]
          exact (congrFun (LinearMap.mem_ker.mp y.property.2) ⟨e, h⟩).symm
      have y_cycle : y.val ∈ coordinateCycleSpace source target := y.property.1
      have x_cycle : x ∈ cycle :=
        (extendChain_mem_coordinateCycleSpace_iff source target selected x).mp (ext_eq ▸ y_cycle)
      exact ⟨⟨x, x_cycle⟩, Subtype.ext ext_eq⟩

end Unfoldings
