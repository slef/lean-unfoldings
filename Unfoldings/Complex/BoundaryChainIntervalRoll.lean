module

public import Unfoldings.Complex.BoundaryChainIntervalHeading
public import Unfoldings.Geometry.ChainInterval
public import Unfoldings.Geometry.ComplexRotation

/-! Rolling a consecutive window changes its orientation and starting position by an isometry. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam} {n : ℕ} (chain : (C.boundarySystem retain).Chain n)
  (first length : ℕ) (fits : first + length ≤ n)

local notation "R" => complexRotation
  (-C.boundaryChainRollHeading chain (chain.intervalIndex first length fits 0))
local notation "A" => PolygonalChain.interval (C.boundaryChainRoll chain) first (length + 1) (by omega)
local notation "D" => C.boundaryChainRoll (chain.interval first length fits)

/-- Edges of the rolled subchain differ from the same rolled full-chain edges by one rotation. -/
theorem boundaryChainRoll_interval_edge (i : Fin (length + 1)) :
    (D).edge i = (R) ((A).edge i) := by
  rw [PolygonalChain.interval_edge]
  have index : (⟨first + i.val, by omega⟩ : Fin (n + 1)) =
      chain.intervalIndex first length fits i := rfl
  unfold boundaryChainRoll
  rw [PolygonalChain.ofHeadings_edge, index, PolygonalChain.ofHeadings_edge,
    C.boundaryChainRollHeading_interval, PairedInvolutions.System.Chain.interval_point]
  rw [sub_eq_add_neg, polarRay_add]
  change _ = polarRay (-C.boundaryChainRollHeading chain
    (chain.intervalIndex first length fits 0)) * _
  ring

/-- The same rotation relates every prefix chord of the actual rolled window. -/
theorem boundaryChainRoll_interval_chord (i : Fin (length + 2)) :
    (D).vertex i - (D).vertex 0 = (R) ((A).vertex i - (A).vertex 0) := by
  induction i using Fin.induction with
  | zero => simp only [sub_self, map_zero]
  | succ k ih =>
    have chord (P : PolygonalChain ℂ (length + 1)) :
        P.vertex k.succ - P.vertex 0 = (P.vertex k.castSucc - P.vertex 0) + P.edge k := by
      simp only [PolygonalChain.edge]
      ring
    rw [chord (D), chord (A), ih, C.boundaryChainRoll_interval_edge chain first length fits k,
      map_add]

/-- Length needs no information about the initial heading of the rolled subchain. -/
theorem boundaryChainRoll_interval_projectedLength :
    (D).projectedLength = (A).projectedLength := by
  unfold PolygonalChain.projectedLength
  apply Finset.sum_congr rfl
  intro i _
  exact (congrArg norm (C.boundaryChainRoll_interval_edge chain first length fits i)).trans
    ((R).norm_map _)

end Unfoldings.TriangleComplex
