module

public import Unfoldings.Complex.RawGermChains
public import Unfoldings.Complex.BoundaryLink

/-! Matching actual terminal bank germs identifies original fans across whole-face restriction. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam} (U : Set Face)

open Classical in
/-- The two actual terminal germs identify every ordered original corner and its weight.
The selected-face restriction may have a different vertex type and a different fan length;
these identifications are derived rather than assumed. -/
theorem sum_fan_weights_eq_restricted_of_terminal_germs
    (p : C.BoundaryEnd retain) (q : (C.restrictFaces U).BoundaryEnd Set.univ)
    (initial : p.val = C.includeRestrictedGerm U q.val)
    (terminal : (C.boundaryMate retain p).val = C.includeRestrictedGerm U
      ((C.restrictFaces U).boundaryMate Set.univ q).val)
    (weight : C.Corner → ℝ) :
    (∑ a : C.Corner, if C.vertexOfCorner retain a = C.boundaryEndVertex retain p
      then weight a else 0) =
    ∑ b : (C.restrictFaces U).Corner,
      if (C.restrictFaces U).vertexOfCorner Set.univ b =
        (C.restrictFaces U).boundaryEndVertex Set.univ q then weight (b.1.val, b.2) else 0 := by
  classical
  let R := C.restrictFaces U
  obtain ⟨n, c, first_c, last_c, covers_c⟩ := C.exists_boundary_link retain p
  obtain ⟨m, d, first_d, last_d, covers_d⟩ := R.exists_boundary_link Set.univ q
  let left := C.rawLinkChain c
  let right := C.rawRestrictedLinkChain U d
  have first : left.first = right.first := by
    change c.first.val = C.includeRestrictedGerm U d.first.val
    rw [first_c, first_d]
    exact initial
  have last : C.rawGermSystem.turn left.last = C.rawGermSystem.turn right.last := by
    change (C.linkTurn retain _ c.last).val =
      C.includeRestrictedGerm U (R.linkTurn Set.univ _ d.last).val
    rw [last_c, last_d]
    exact terminal
  obtain ⟨length, points⟩ := left.eq_length_and_points_of_terminals right first last
  have first_sum := C.sum_ordered_link_corner_weights c covers_c weight
  have last_sum := R.sum_ordered_link_corner_weights d covers_d
    (fun b => weight (b.1.val, b.2))
  rw [← first_sum, ← last_sum]
  subst m
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun germ : C.Germ => weight germ.1) (points i i rfl)

open Classical in
/-- In particular the actual intrinsic angle agrees with the selected-face fan angle. -/
theorem totalAngle_eq_restricted_of_terminal_germs
    (p : C.BoundaryEnd retain) (q : (C.restrictFaces U).BoundaryEnd Set.univ)
    (initial : p.val = C.includeRestrictedGerm U q.val)
    (terminal : (C.boundaryMate retain p).val = C.includeRestrictedGerm U
      ((C.restrictFaces U).boundaryMate Set.univ q).val) :
    C.totalAngle retain (C.boundaryEndVertex retain p) =
      (C.restrictFaces U).totalAngle Set.univ
        ((C.restrictFaces U).boundaryEndVertex Set.univ q) :=
  C.sum_fan_weights_eq_restricted_of_terminal_germs U p q initial terminal _

end Unfoldings.TriangleComplex
