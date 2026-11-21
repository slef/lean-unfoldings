module

public import Unfoldings.Combinatorics.CoordinateCycles

/-! Component counts for a pair of finite primal and dual graphs whose face
boundaries span the primal cycles. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Module

variable {V F E K : Type*} [Fintype V] [Fintype E] [Field K]
  (source target : E → V) (left right : E → F)

private theorem finrank_ker_edgeCoboundary {A B : Type*}
    (source target : A → B) [Finite B] :
    finrank K (edgeCoboundary source target K).ker =
      Nat.card (endpointGraph source target).ConnectedComponent := by
  let : Fintype (endpointGraph source target).ConnectedComponent := Fintype.ofFinite _
  rw [← (componentPotentialEquiv source target K).finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

/-- On a connected sphere Euler's identity upgrades the cycle condition for
dual coboundaries to exactness of the full primal cycle space. -/
theorem range_edgeCoboundary_eq_coordinateCycleSpace [Fintype F]
    (primal_connected : Nat.card (endpointGraph source target).ConnectedComponent = 1)
    (dual_connected : Nat.card (endpointGraph left right).ConnectedComponent = 1)
    (euler : (Fintype.card V : ℤ) - Fintype.card E + Fintype.card F = 2)
    (cycles : LinearMap.range (edgeCoboundary left right K) ≤
      coordinateCycleSpace (K := K) source target) :
    LinearMap.range (edgeCoboundary left right K) = coordinateCycleSpace source target := by
  apply Submodule.eq_of_le_of_finrank_le cycles
  have primal := finrank_coordinateCycleSpace_add_card_vertex (K := K) source target
  rw [primal_connected] at primal
  have dual := (edgeCoboundary left right K).finrank_range_add_finrank_ker
  rw [finrank_ker_edgeCoboundary, dual_connected, Module.finrank_fintype_fun_eq_card] at dual
  omega

variable (cut : E → Prop) [DecidablePred cut]

omit [Fintype V] in
/-- With dual edges retained exactly across uncut seams, each independent
cycle of the primal cut graph adds a component to the retained dual graph. -/
theorem dual_components_eq_cut_cycle_rank [Finite F]
    (exactness : LinearMap.range (edgeCoboundary left right K) =
      coordinateCycleSpace (K := K) source target) :
    Nat.card (endpointGraph (left ∘ (Subtype.val : {e // ¬ cut e} → E))
      (right ∘ Subtype.val)).ConnectedComponent =
      Nat.card (endpointGraph left right).ConnectedComponent +
        finrank K (coordinateCycleSpace (K := K)
          (source ∘ (Subtype.val : {e // cut e} → E)) (target ∘ Subtype.val)) := by
  let full := edgeCoboundary left right K
  let retained := edgeCoboundary (left ∘ (Subtype.val : {e // ¬ cut e} → E))
    (right ∘ Subtype.val) K
  let excluded := LinearMap.funLeft K K (Subtype.val : {e // ¬ cut e} → E)
  let supported := coordinateCycleSpace (K := K) source target ⊓ LinearMap.ker excluded
  let restricted : retained.ker →ₗ[K] supported :=
    (full.comp retained.ker.subtype).codRestrict _ (by
      intro x
      exact ⟨exactness ▸ LinearMap.mem_range_self full x.val, x.property⟩)
  have surjective : Function.Surjective restricted := by
    intro z
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (exactness.symm ▸ z.property.1)
    have x_mem : x ∈ retained.ker := by
      apply LinearMap.mem_ker.mpr
      have restriction := LinearMap.mem_ker.mp z.property.2
      change excluded (full x) = 0
      rwa [hx]
    exact ⟨⟨x, x_mem⟩, Subtype.ext hx⟩
  have kernel : restricted.ker = full.ker.comap retained.ker.subtype := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap, LinearMap.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have contains : full.ker ≤ retained.ker := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    change excluded (full x) = 0
    rw [LinearMap.mem_ker.mp hx, map_zero]
  have dimension := restricted.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr surjective, finrank_top, kernel,
    (Submodule.comapSubtypeEquivOfLe contains).finrank_eq,
    ← (selectedCycleEquiv (K := K) source target cut).finrank_eq] at dimension
  change _ + finrank K (edgeCoboundary left right K).ker =
    finrank K (edgeCoboundary (left ∘ (Subtype.val : {e // ¬ cut e} → E))
      (right ∘ Subtype.val) K).ker at dimension
  rw [finrank_ker_edgeCoboundary, finrank_ker_edgeCoboundary] at dimension
  omega

end Unfoldings
