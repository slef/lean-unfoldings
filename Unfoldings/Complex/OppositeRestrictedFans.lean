module

public import Unfoldings.Complex.RawLinkComplement
public import Unfoldings.Complex.RestrictedCutFanAgreement

/-! Opposite actual retained fans exhaust the original vertex's complete corner star. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

local instance oppositeRestrictedFanMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U V : Set Face)
  {leftRetain : Set (C.restrictFaces U).Seam}
  {rightRetain : Set (C.restrictFaces V).Seam}
  (p : (C.restrictFaces U).BoundaryEnd leftRetain)
  (q : (C.restrictFaces V).BoundaryEnd rightRetain)

open Classical in
/-- The two actual fans partition every original corner weight when their terminal banks
are paired across the two original seams. Neither angle nor corner-set matches are assumed. -/
theorem sum_opposite_restricted_fan_weights
    (internal : ¬ C.IsBoundaryVertex Set.univ
      (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U p.val).1))
    (initial : C.includeRestrictedGerm V q.val = C.mateGerm Set.univ
      (C.includeRestrictedGerm U p.val))
    (terminal : C.includeRestrictedGerm V ((C.restrictFaces V).boundaryMate rightRetain q).val =
      C.mateGerm Set.univ
        (C.includeRestrictedGerm U ((C.restrictFaces U).boundaryMate leftRetain p).val))
    (different : C.includeRestrictedGerm V ((C.restrictFaces V).boundaryMate rightRetain q).val ≠
      C.includeRestrictedGerm U p.val) (weight : C.Corner → ℝ) :
    (∑ a : (C.restrictFaces U).Corner,
      if (C.restrictFaces U).vertexOfCorner leftRetain a =
        (C.restrictFaces U).boundaryEndVertex leftRetain p then weight (a.1.val, a.2) else 0) +
      (∑ b : (C.restrictFaces V).Corner,
        if (C.restrictFaces V).vertexOfCorner rightRetain b =
          (C.restrictFaces V).boundaryEndVertex rightRetain q then weight (b.1.val, b.2) else 0) =
      C.regionalCornerSum Set.univ weight
        (C.vertexOfCorner Set.univ (C.includeRestrictedGerm U p.val).1) := by
  let R := C.restrictFaces U
  let S := C.restrictFaces V
  obtain ⟨n, c, first_c, last_c, covers_c⟩ := R.exists_boundary_link leftRetain p
  obtain ⟨m, d, first_d, last_d, covers_d⟩ := S.exists_boundary_link rightRetain q
  let left := C.rawRestrictedRetainedLinkChain U c
  let right := C.rawRestrictedRetainedLinkChain V d
  have raw_first : left.first = C.includeRestrictedGerm U p.val := by
    change C.includeRestrictedGerm U c.first.val = _
    rw [first_c]
  have first : right.first = C.mateGerm Set.univ left.first := by
    change C.includeRestrictedGerm V d.first.val =
      C.mateGerm Set.univ (C.includeRestrictedGerm U c.first.val)
    rw [first_c, first_d]
    exact initial
  have last : C.turnGerm right.last = C.mateGerm Set.univ (C.turnGerm left.last) := by
    change C.includeRestrictedGerm V (S.linkTurn rightRetain _ d.last).val =
      C.mateGerm Set.univ (C.includeRestrictedGerm U (R.linkTurn leftRetain _ c.last).val)
    rw [last_c, last_d]
    exact terminal
  have distinct : C.turnGerm right.last ≠ left.first := by
    change C.includeRestrictedGerm V (S.linkTurn rightRetain _ d.last).val ≠
      C.includeRestrictedGerm U c.first.val
    rw [last_d, first_c]
    exact different
  have original_internal : ¬ C.IsBoundaryVertex Set.univ
      (C.vertexOfCorner Set.univ left.first.1) := by rwa [raw_first]
  have weights := C.sum_opposite_raw_linkCornerWeight left right original_internal
    first last distinct weight
  rw [raw_first] at weights
  rw [← R.sum_ordered_link_corner_weights c covers_c (fun a => weight (a.1.val, a.2)),
    ← S.sum_ordered_link_corner_weights d covers_d (fun b => weight (b.1.val, b.2))]
  exact weights

end Unfoldings.TriangleComplex
