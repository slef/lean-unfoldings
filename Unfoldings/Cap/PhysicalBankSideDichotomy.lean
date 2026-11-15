module

public import Unfoldings.Cap.ProjectedUnsignedBankRays
public import Unfoldings.Cap.SignedJordanBankPropagation
public import Unfoldings.Cap.PhysicalBoundaryChainLift

/-! Physical actual chains consistently choose the same or opposite original bank side. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

local instance physicalBankDichotomyMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U : Set Face) {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
  (c : ((C.restrictFaces U).boundarySystem retain).Chain n)

/-- The occupied-side sign of every actual bank is exactly its initial sign. -/
theorem projected_restricted_chain_positive_iff (i : Fin (n + 1)) :
    (0 < K.projectedGermOrientation (C.includeRestrictedGerm U (c.point i).val)) ↔
      0 < K.projectedGermOrientation (C.includeRestrictedGerm U c.first.val) := by
  induction i using Fin.induction with
  | zero => rfl
  | succ k previous =>
    have product := K.projected_restricted_boundary_successor_sign U
      (c.point k.castSucc) (c.point k.succ) (c.next k)
    have step :
        (0 < K.projectedGermOrientation (C.includeRestrictedGerm U (c.point k.succ).val)) ↔
          0 < K.projectedGermOrientation (C.includeRestrictedGerm U (c.point k.castSucc).val) := by
      rcases mul_pos_iff.mp product with ⟨apos, bpos⟩ | ⟨aneg, bneg⟩
      · exact iff_of_true bpos apos
      · exact iff_of_false (not_lt.mpr bneg.le) (not_lt.mpr aneg.le)
    exact step.trans previous

variable (V : Set Face) {rightRetain : Set (C.restrictFaces V).Seam}
  (d : ((C.restrictFaces V).boundarySystem rightRetain).Chain n)

/-- Actual physical chain matching is globally on the same original side or globally
on the opposite seam side. It cannot switch sides independently at different hinges. -/
theorem restricted_physical_boundary_chain_bank_dichotomy
    (positions : ∀ i, (K.folding.restrictFaces V).boundaryPosition (d.point i) =
      (K.folding.restrictFaces U).boundaryPosition (c.point i))
    (vectors : ∀ i, (K.folding.restrictFaces V).germDirection (d.point i).val =
      (K.folding.restrictFaces U).germDirection (c.point i).val)
    (internal : ∀ i, ¬ C.IsBoundaryVertex Set.univ
      (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (c.point i).val).1)) :
    (∀ i, C.includeRestrictedGerm V (d.point i).val = C.includeRestrictedGerm U (c.point i).val) ∨
      ∀ i, C.includeRestrictedGerm V (d.point i).val =
        C.mateGerm Set.univ (C.includeRestrictedGerm U (c.point i).val) := by
  have apex (i) : (K.projectedTriangle (d.point i).val.1.1.val).vertex (d.point i).val.1.2 =
      (K.projectedTriangle (c.point i).val.1.1.val).vertex (c.point i).val.1.2 := by
    simpa only [SpatialFolding.boundaryPosition_raw] using! congrArg Cap.horizontal (positions i)
  have rays (i) : Cap.horizontal
      (K.folding.germDirection (C.includeRestrictedGerm V (d.point i).val)) =
    Cap.horizontal (K.folding.germDirection (C.includeRestrictedGerm U (c.point i).val)) :=
    congrArg Cap.horizontal (vectors i)
  by_cases same_side :
      (0 < K.projectedGermOrientation (C.includeRestrictedGerm V d.first.val)) ↔
        0 < K.projectedGermOrientation (C.includeRestrictedGerm U c.first.val)
  · left
    intro i
    have signs := (K.projected_restricted_chain_positive_iff V d i).trans
      (same_side.trans (K.projected_restricted_chain_positive_iff U c i).symm)
    have product : 0 < K.projectedGermOrientation (C.includeRestrictedGerm V (d.point i).val) *
        K.projectedGermOrientation (C.includeRestrictedGerm U (c.point i).val) := by
      rcases lt_or_gt_of_ne (K.projectedGermOrientation_ne_zero
        (C.includeRestrictedGerm U (c.point i).val)) with negative | positive
      · have other : K.projectedGermOrientation (C.includeRestrictedGerm V (d.point i).val) < 0 :=
          lt_of_le_of_ne (le_of_not_gt (fun h => negative.not_gt (signs.mp h)))
            (K.projectedGermOrientation_ne_zero _)
        exact mul_pos_of_neg_of_neg other negative
      · exact mul_pos (signs.mpr positive) positive
    exact K.projected_raw_germ_unique _ _ (apex i) product (rays i)
  · right
    intro i
    have original : C.vertexOfCorner Set.univ (C.includeRestrictedGerm V (d.point i).val).1 =
        C.vertexOfCorner Set.univ (C.includeRestrictedGerm U (c.point i).val).1 :=
      K.projectedVertex_injective (apex i)
    have internal_d : ¬ C.IsBoundaryVertex Set.univ
        (C.vertexOfCorner Set.univ (C.includeRestrictedGerm V (d.point i).val).1) :=
      original.symm ▸ internal i
    have ray : Cap.horizontal
        (K.folding.germDirection (C.includeRestrictedGerm V (d.point i).val)) =
      (1 : ℝ) • Cap.horizontal
        (K.folding.germDirection (C.includeRestrictedGerm U (c.point i).val)) := by
      simpa only [one_smul] using rays i
    rcases K.projected_raw_germ_eq_or_mate_of_positive_scale _ _ (apex i)
        internal_d zero_lt_one ray with same | opposite
    · apply (same_side ?_).elim
      have at_i :
          (0 < K.projectedGermOrientation (C.includeRestrictedGerm V (d.point i).val)) ↔
            0 < K.projectedGermOrientation (C.includeRestrictedGerm U (c.point i).val) := by
        rw [same]
      exact (K.projected_restricted_chain_positive_iff V d i).symm.trans
        (at_i.trans (K.projected_restricted_chain_positive_iff U c i))
    · exact opposite

end Unfoldings.ConvexCap
