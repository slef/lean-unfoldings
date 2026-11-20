module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The cycle rank of a finite graph with individually indexed, oriented edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Module

variable {V E : Type*} (source target : E → V)

/-- The adjacency graph determines the components. Individual edges retain their
indices in the incidence maps, so both parallel edges and loops are allowed. -/
def endpointGraph : SimpleGraph V :=
  SimpleGraph.fromRel fun v w => ∃ e, source e = v ∧ target e = w

variable (K : Type*) [Field K]

/-- The difference of endpoint potentials on every directed edge. -/
def edgeCoboundary : (V → K) →ₗ[K] (E → K) :=
  LinearMap.pi fun e =>
    (LinearMap.proj (target e) : (V → K) →ₗ[K] K) - LinearMap.proj (source e)

@[simp] theorem edgeCoboundary_apply (f : V → K) (e : E) :
    edgeCoboundary source target K f e = f (target e) - f (source e) := rfl

/-- The edge chains with zero vertex boundary, expressed in the dual of edge potentials. -/
def edgeCycleSpace : Submodule K (Module.Dual K (E → K)) :=
  LinearMap.ker (edgeCoboundary source target K).dualMap

/-- The coboundary kernel consists exactly of arbitrary potentials on components. -/
def componentPotentialEquiv :
    ((endpointGraph source target).ConnectedComponent → K) ≃ₗ[K]
      LinearMap.ker (edgeCoboundary source target K) := by
  let G := endpointGraph source target
  have equal_at_ends (e : E) :
      G.connectedComponentMk (source e) = G.connectedComponentMk (target e) := by
    by_cases loop : source e = target e
    · rw [loop]
    · exact SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable
        ((SimpleGraph.fromRel_adj _ _ _).2 ⟨loop, Or.inl ⟨e, rfl, rfl⟩⟩))
  let potential : (G.ConnectedComponent → K) →ₗ[K] (V → K) :=
    LinearMap.pi fun v =>
      (LinearMap.proj (G.connectedComponentMk v) : (G.ConnectedComponent → K) →ₗ[K] K)
  let restricted : (G.ConnectedComponent → K) →ₗ[K]
      LinearMap.ker (edgeCoboundary source target K) := potential.codRestrict _ (by
    intro f
    apply LinearMap.mem_ker.mpr
    funext e
    change f (G.connectedComponentMk (target e)) - f (G.connectedComponentMk (source e)) = 0
    rw [equal_at_ends, sub_self])
  apply LinearEquiv.ofBijective restricted
  constructor
  · intro f h equal
    funext c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      exact congrArg (fun g : LinearMap.ker (edgeCoboundary source target K) => g.val v) equal
  · intro f
    have edge_equal (e : E) : f.val (source e) = f.val (target e) := by
      have zero := congrFun (LinearMap.mem_ker.mp f.property) e
      exact (sub_eq_zero.mp zero).symm
    have adjacent {v w : V} (edge : G.Adj v w) : f.val v = f.val w := by
      obtain ⟨_, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).mp edge
      · obtain ⟨e, rfl, rfl⟩ := h
        exact edge_equal e
      · obtain ⟨e, rfl, rfl⟩ := h
        exact (edge_equal e).symm
    have along_walk {v w : V} (walk : G.Walk v w) : f.val v = f.val w := by
      induction walk with
      | nil => rfl
      | cons edge _ tail => exact (adjacent edge).trans tail
    refine ⟨SimpleGraph.ConnectedComponent.lift f.val (fun _ _ walk _ => along_walk walk), ?_⟩
    apply Subtype.ext
    funext v
    rfl

/-- Cycle rank equals edge count minus vertex count plus component count. -/
theorem finrank_edgeCycleSpace_add_card_vertex [Fintype V] [Fintype E] :
    finrank K (edgeCycleSpace source target K) + Fintype.card V =
      Fintype.card E + Nat.card (endpointGraph source target).ConnectedComponent := by
  classical
  let G := endpointGraph source target
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let coboundary := edgeCoboundary source target K
  have kernel :
      finrank K (LinearMap.ker coboundary) = Nat.card G.ConnectedComponent := by
    rw [← (componentPotentialEquiv source target K).finrank_eq,
      Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]
  have potentials := coboundary.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card, kernel] at potentials
  have chains := coboundary.dualMap.finrank_range_add_finrank_ker
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range, Subspace.dual_finrank_eq,
    Module.finrank_fintype_fun_eq_card] at chains
  change finrank K (LinearMap.ker coboundary.dualMap) + _ = _ + Nat.card G.ConnectedComponent
  omega

end Unfoldings
