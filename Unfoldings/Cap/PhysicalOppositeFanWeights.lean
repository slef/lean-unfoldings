module

public import Unfoldings.Cap.PhysicalBankSideDichotomy
public import Unfoldings.Complex.OppositeRestrictedFans
public import Unfoldings.Complex.EdgeReverseGerm

/-! Opposite physical bank chains have exactly complementary original corner fans. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

local instance physicalOppositeFanMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U : Set Face) {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
  (c : ((C.restrictFaces U).boundarySystem retain).Chain n)

/-- A simple physical path cannot have a full-star fan that immediately retraces one edge. -/
theorem boundary_chain_terminal_mate_ne_of_simple
    (simple : Function.Injective (K.projectedBoundaryChain U c).vertex) (k : Fin n) :
    C.mateGerm Set.univ (C.includeRestrictedGerm U
      ((C.restrictFaces U).boundaryMate retain (c.point k.succ)).val) ≠
        C.includeRestrictedGerm U (c.point k.succ).val := by
  intro equal
  have direction : Cap.horizontal ((K.folding.restrictFaces U).germDirection
      ((C.restrictFaces U).boundaryMate retain (c.point k.succ)).val) =
    Cap.horizontal ((K.folding.restrictFaces U).germDirection (c.point k.succ).val) := by
    change Cap.horizontal (K.folding.germDirection (C.includeRestrictedGerm U
      ((C.restrictFaces U).boundaryMate retain (c.point k.succ)).val)) =
        Cap.horizontal (K.folding.germDirection (C.includeRestrictedGerm U (c.point k.succ).val))
    rw [← equal, K.folding.germDirection_mate]
  have rays := K.projectedBoundaryChain_internal_rays U c k
  rw [rays.2, rays.1] at direction
  have vertices : (K.projectedBoundaryChain U c).vertex k.castSucc.castSucc =
      (K.projectedBoundaryChain U c).vertex k.succ.succ := by
    simpa only [sub_add_cancel] using congrArg
      (fun z : Plane => z + (K.projectedBoundaryChain U c).vertex k.succ.castSucc) direction
  have indices := simple vertices
  have values := congrArg Fin.val indices
  simp only [Fin.val_castSucc, Fin.val_succ] at values
  omega

variable (V : Set Face) {rightRetain : Set (C.restrictFaces V).Seam}
  (d : ((C.restrictFaces V).boundarySystem rightRetain).Chain n)
  (banks : ∀ i, C.includeRestrictedGerm V (d.point i).val =
    C.mateGerm Set.univ (C.includeRestrictedGerm U (c.point i).val))

include banks in
/-- Opposite outgoing original banks also identify both actual incoming terminal banks. -/
theorem opposite_chain_terminal_germs (k : Fin n) :
    C.includeRestrictedGerm V
      ((C.restrictFaces V).boundaryMate rightRetain (d.point k.succ)).val =
      C.mateGerm Set.univ
        (C.includeRestrictedGerm U
          ((C.restrictFaces U).boundaryMate retain (c.point k.succ)).val) := by
  have left : (C.restrictFaces U).boundaryMate retain (c.point k.succ) =
      (C.restrictFaces U).boundaryTurn retain (c.point k.castSucc) := c.mate_succ k
  have right : (C.restrictFaces V).boundaryMate rightRetain (d.point k.succ) =
      (C.restrictFaces V).boundaryTurn rightRetain (d.point k.castSucc) := d.mate_succ k
  rw [left, right, C.includeRestrictedGerm_boundaryTurn, C.includeRestrictedGerm_boundaryTurn]
  change C.edgeReverseGerm (C.includeRestrictedGerm V (d.point k.castSucc).val) =
    C.mateGerm Set.univ (C.edgeReverseGerm (C.includeRestrictedGerm U (c.point k.castSucc).val))
  rw [banks, C.mateGerm_edgeReverse]

include banks in
open Classical in
/-- All original corner weights in the two actual one-sided fans sum to the full old star.
The fan separation and completeness follow from physical path simplicity and old seam pairings. -/
theorem sum_opposite_physical_chain_fan_weights
    (simple : Function.Injective (K.projectedBoundaryChain U c).vertex) (k : Fin n)
    (internal : ¬ C.IsBoundaryVertex Set.univ
      (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (c.point k.succ).val).1))
    (weight : C.Corner → ℝ) :
    (∑ a : (C.restrictFaces U).Corner,
      if (C.restrictFaces U).vertexOfCorner retain a =
        (C.restrictFaces U).boundaryEndVertex retain (c.point k.succ)
      then weight (a.1.val, a.2) else 0) +
    (∑ b : (C.restrictFaces V).Corner,
      if (C.restrictFaces V).vertexOfCorner rightRetain b =
        (C.restrictFaces V).boundaryEndVertex rightRetain (d.point k.succ)
      then weight (b.1.val, b.2) else 0) =
      C.regionalCornerSum Set.univ weight
        (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (c.point k.succ).val).1) := by
  apply C.sum_opposite_restricted_fan_weights U V (c.point k.succ) (d.point k.succ)
    internal (banks k.succ) (opposite_chain_terminal_germs U c V d banks k)
  rw [opposite_chain_terminal_germs U c V d banks k]
  exact K.boundary_chain_terminal_mate_ne_of_simple U c simple k

end Unfoldings.ConvexCap
