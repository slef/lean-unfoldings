module

public import Unfoldings.Complex.RestrictedBoundaryChainAgreement

/-! Arbitrary original corner weights agree along matching actual bank chains. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

local instance restrictedChainWeightMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U V : Set Face)
  {leftRetain : Set (C.restrictFaces U).Seam}
  {rightRetain : Set (C.restrictFaces V).Seam} {n : ℕ}
  (c : ((C.restrictFaces U).boundarySystem leftRetain).Chain n)
  (d : ((C.restrictFaces V).boundarySystem rightRetain).Chain n)
  (banks : ∀ i, C.includeRestrictedGerm U (c.point i).val =
    C.includeRestrictedGerm V (d.point i).val)

include banks in
/-- The incoming terminal germs are the actual reverses of the preceding banks. -/
theorem restricted_boundary_chain_terminal_germs (i : Fin n) :
    C.includeRestrictedGerm U ((C.restrictFaces U).boundaryMate leftRetain (c.point i.succ)).val =
      C.includeRestrictedGerm V
        ((C.restrictFaces V).boundaryMate rightRetain (d.point i.succ)).val := by
  have left : (C.restrictFaces U).boundaryMate leftRetain (c.point i.succ) =
      (C.restrictFaces U).boundaryTurn leftRetain (c.point i.castSucc) := c.mate_succ i
  have right : (C.restrictFaces V).boundaryMate rightRetain (d.point i.succ) =
      (C.restrictFaces V).boundaryTurn rightRetain (d.point i.castSucc) := d.mate_succ i
  rw [left, right, C.includeRestrictedGerm_boundaryTurn, C.includeRestrictedGerm_boundaryTurn]
  simpa only using! congrArg
    (fun p : C.Germ => C.germOfEndpoint (C.germEdge p) (!p.2)) (banks i.castSucc)

include banks in
open Classical in
/-- The full one-sided original corner selection preserves every weight, including
actual projected angles, rather than just intrinsic angle totals. -/
theorem sum_restricted_chain_corner_weights_eq (weight : C.Corner → ℝ) (i : Fin n) :
    (∑ a : (C.restrictFaces U).Corner,
      if (C.restrictFaces U).vertexOfCorner leftRetain a =
        (C.restrictFaces U).boundaryEndVertex leftRetain (c.point i.succ)
      then weight (a.1.val, a.2) else 0) =
    ∑ b : (C.restrictFaces V).Corner,
      if (C.restrictFaces V).vertexOfCorner rightRetain b =
        (C.restrictFaces V).boundaryEndVertex rightRetain (d.point i.succ)
      then weight (b.1.val, b.2) else 0 :=
  C.sum_restricted_fan_weights_eq_of_terminal_germs U V _ _ (banks i.succ)
    (C.restricted_boundary_chain_terminal_germs U V c d banks i) weight

end Unfoldings.TriangleComplex
