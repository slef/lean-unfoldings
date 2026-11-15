module

public import Unfoldings.Cap.PhysicalOppositeFanError
public import Unfoldings.Cap.OriginalChainCurvature

/-! Exact physical bank-chain geometry compares either actual fan side at total-curvature cost. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

local instance physicalChainErrorMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U V : Set Face)
  {leftRetain : Set (C.restrictFaces U).Seam}
  {rightRetain : Set (C.restrictFaces V).Seam} {n : ℕ}
  (c : ((C.restrictFaces U).boundarySystem leftRetain).Chain n)
  (d : ((C.restrictFaces V).boundarySystem rightRetain).Chain n)

/-- The actual fan errors of physically matching bank chains differ, up to reversal,
by at most total original curvature. All fan correspondences and charges are derived. -/
theorem abs_sum_cut_turnError_le_of_physical_chain_geometry
    (positions : ∀ i, (K.folding.restrictFaces V).boundaryPosition (d.point i) =
      (K.folding.restrictFaces U).boundaryPosition (c.point i))
    (vectors : ∀ i, (K.folding.restrictFaces V).germDirection (d.point i).val =
      (K.folding.restrictFaces U).germDirection (c.point i).val)
    (simple : Function.Injective (K.projectedBoundaryChain U c).vertex)
    (internal : ∀ i, ¬ C.IsBoundaryVertex Set.univ
      (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (c.point i).val).1)) :
    |∑ k : Fin n, K.cutBoundaryTurnError U (c.point k.succ)| ≤
      C.totalInteriorAngularDefect Set.univ +
        |∑ k : Fin n, K.cutBoundaryTurnError V (d.point k.succ)| := by
  have nonnegative : 0 ≤ C.totalInteriorAngularDefect Set.univ := by
    simpa only [Finset.sum_empty] using K.sum_interiorAngularDefect_le_totalCurvature ∅
  rcases K.restricted_physical_boundary_chain_bank_dichotomy U c V d positions vectors internal
    with same | opposite
  · have equality : (∑ k : Fin n, K.cutBoundaryTurnError U (c.point k.succ)) =
        ∑ k : Fin n, K.cutBoundaryTurnError V (d.point k.succ) :=
      Finset.sum_congr rfl (fun k _ =>
        (K.cutBoundaryTurnError_eq_of_original_banks V U d c same k).symm)
    rw [equality]
    exact le_add_of_nonneg_left nonnegative
  · have equality : (∑ k : Fin n, K.cutBoundaryTurnError U (c.point k.succ)) +
        (∑ k : Fin n, K.cutBoundaryTurnError V (d.point k.succ)) =
        ∑ k : Fin n, C.interiorAngularDefect Set.univ
          (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (c.point k.succ).val).1) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ =>
        K.opposite_physical_chain_turnErrors_add U V c d opposite simple k (internal k.succ))
    have budget := K.sum_original_chain_internal_curvature_le_total U c simple
    have positive : 0 ≤ ∑ k : Fin n, C.interiorAngularDefect Set.univ
        (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (c.point k.succ).val).1) :=
      Finset.sum_nonneg (fun _ _ => K.interiorCurvature_nonneg _)
    have lower := neg_abs_le (∑ k : Fin n, K.cutBoundaryTurnError V (d.point k.succ))
    have upper := le_abs_self (∑ k : Fin n, K.cutBoundaryTurnError V (d.point k.succ))
    apply abs_le.mpr
    constructor <;> linarith

end Unfoldings.ConvexCap
