module

public import Unfoldings.Cap.PhysicalOppositeFanWeights
public import Unfoldings.Cap.OriginalChainTurnError

/-! Actual opposite cut-bank fan errors add to the original vertex curvature. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

local instance physicalOppositeErrorMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

open Classical in
/-- The actual cut fan's turn error is minus its original intrinsic/projected corner excess. -/
theorem cutBoundaryTurnError_eq_neg_corner_excess (U : Set Face)
    {retain : Set (C.restrictFaces U).Seam} (p : (C.restrictFaces U).BoundaryEnd retain) :
    K.cutBoundaryTurnError U p =
      -(∑ a : (C.restrictFaces U).Corner,
        if (C.restrictFaces U).vertexOfCorner retain a =
          (C.restrictFaces U).boundaryEndVertex retain p then
          (C.triangle a.1.val).cornerAngle a.2 - (K.projectedTriangle a.1.val).cornerAngle a.2
        else 0) := by
  let R := C.restrictFaces U
  let w := R.boundaryEndVertex retain p
  have split : (∑ a : R.Corner, if R.vertexOfCorner retain a = w then
      (R.triangle a.1).cornerAngle a.2 - (K.projectedTriangle a.1.val).cornerAngle a.2 else 0) =
      (∑ a : R.Corner, if R.vertexOfCorner retain a = w then (R.triangle a.1).cornerAngle a.2
        else 0) -
      (∑ a : R.Corner, if R.vertexOfCorner retain a = w then
        (K.projectedTriangle a.1.val).cornerAngle a.2 else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  dsimp only [cutBoundaryTurnError, projectedCutFanAngle, TriangleComplex.totalAngle]
  change (Real.pi - ∑ a : R.Corner, if R.vertexOfCorner retain a = w then
      (R.triangle a.1).cornerAngle a.2 else 0) -
    (Real.pi - ∑ a : R.Corner, if R.vertexOfCorner retain a = w then
      (K.projectedTriangle a.1.val).cornerAngle a.2 else 0) =
    -(∑ a : R.Corner, if R.vertexOfCorner retain a = w then
      (R.triangle a.1).cornerAngle a.2 - (K.projectedTriangle a.1.val).cornerAngle a.2 else 0)
  rw [split]
  ring

variable (U V : Set Face)
  {leftRetain : Set (C.restrictFaces U).Seam}
  {rightRetain : Set (C.restrictFaces V).Seam} {n : ℕ}
  (c : ((C.restrictFaces U).boundarySystem leftRetain).Chain n)
  (d : ((C.restrictFaces V).boundarySystem rightRetain).Chain n)
  (banks : ∀ i, C.includeRestrictedGerm V (d.point i).val =
    C.mateGerm Set.univ (C.includeRestrictedGerm U (c.point i).val))

include banks in
/-- Opposite physical fan errors pay exactly the original curvature at this internal hinge. -/
theorem opposite_physical_chain_turnErrors_add
    (simple : Function.Injective (K.projectedBoundaryChain U c).vertex) (k : Fin n)
    (internal : ¬ C.IsBoundaryVertex Set.univ
      (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (c.point k.succ).val).1)) :
    K.cutBoundaryTurnError U (c.point k.succ) + K.cutBoundaryTurnError V (d.point k.succ) =
      C.interiorAngularDefect Set.univ
        (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (c.point k.succ).val).1) := by
  have weights := K.sum_opposite_physical_chain_fan_weights U c V d banks simple k internal
    (fun a => (C.triangle a.1).cornerAngle a.2 - (K.projectedTriangle a.1).cornerAngle a.2)
  have full : C.regionalCornerSum Set.univ
      (fun a => (C.triangle a.1).cornerAngle a.2 - (K.projectedTriangle a.1).cornerAngle a.2)
      (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (c.point k.succ).val).1) =
      -C.interiorAngularDefect Set.univ
        (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (c.point k.succ).val).1) := by
    change K.regionalAngleExcess Set.univ _ = _
    rw [K.regionalAngleExcess_of_fullStar Set.univ _ (fun _ _ => Set.mem_univ _),
      K.projectedTotalAngle_eq_two_pi _ internal]
    simp only [TriangleComplex.interiorAngularDefect, ite_eq_right internal]
    ring
  rw [K.cutBoundaryTurnError_eq_neg_corner_excess, K.cutBoundaryTurnError_eq_neg_corner_excess,
    ← neg_add, weights, full, neg_neg]

end Unfoldings.ConvexCap
