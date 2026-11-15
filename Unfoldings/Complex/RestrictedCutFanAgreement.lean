module

public import Unfoldings.Complex.RestrictedFanAgreement
public import Unfoldings.Complex.RestoredLinkChain

/-! Compare actual cut fans in two independent whole-face restrictions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

open Classical in
/-- A cut link of a whole-face restriction keeps its original raw germ order. -/
def rawRestrictedRetainedLinkChain (U : Set Face)
    {retain : Set (C.restrictFaces U).Seam} {w : (C.restrictFaces U).Vertex retain} {n : ℕ}
    (c : ((C.restrictFaces U).linkSystem retain w).Chain n) : C.rawGermSystem.Chain n :=
  C.rawRestrictedLinkChain U
    ((C.restrictFaces U).restoreLinkChain (Set.subset_univ retain) c)

open Classical in
/-- The two patches may delete different faces and cut different seams. Their actual
terminal germs alone identify every ordered original corner weight. -/
theorem sum_restricted_fan_weights_eq_of_terminal_germs (U V : Set Face)
    {leftRetain : Set (C.restrictFaces U).Seam}
    {rightRetain : Set (C.restrictFaces V).Seam}
    (p : (C.restrictFaces U).BoundaryEnd leftRetain)
    (q : (C.restrictFaces V).BoundaryEnd rightRetain)
    (initial : C.includeRestrictedGerm U p.val = C.includeRestrictedGerm V q.val)
    (terminal : C.includeRestrictedGerm U
        ((C.restrictFaces U).boundaryMate leftRetain p).val =
      C.includeRestrictedGerm V ((C.restrictFaces V).boundaryMate rightRetain q).val)
    (weight : C.Corner → ℝ) :
    (∑ a : (C.restrictFaces U).Corner,
      if (C.restrictFaces U).vertexOfCorner leftRetain a =
        (C.restrictFaces U).boundaryEndVertex leftRetain p then weight (a.1.val, a.2) else 0) =
    ∑ b : (C.restrictFaces V).Corner,
      if (C.restrictFaces V).vertexOfCorner rightRetain b =
        (C.restrictFaces V).boundaryEndVertex rightRetain q then weight (b.1.val, b.2) else 0 := by
  let R := C.restrictFaces U
  let S := C.restrictFaces V
  obtain ⟨n, c, first_c, last_c, covers_c⟩ := R.exists_boundary_link leftRetain p
  obtain ⟨m, d, first_d, last_d, covers_d⟩ := S.exists_boundary_link rightRetain q
  let left := C.rawRestrictedRetainedLinkChain U c
  let right := C.rawRestrictedRetainedLinkChain V d
  have first : left.first = right.first := by
    change C.includeRestrictedGerm U c.first.val = C.includeRestrictedGerm V d.first.val
    rw [first_c, first_d]
    exact initial
  have last : C.rawGermSystem.turn left.last = C.rawGermSystem.turn right.last := by
    change C.includeRestrictedGerm U (R.linkTurn leftRetain _ c.last).val =
      C.includeRestrictedGerm V (S.linkTurn rightRetain _ d.last).val
    rw [last_c, last_d]
    exact terminal
  obtain ⟨length, points⟩ := left.eq_length_and_points_of_terminals right first last
  have first_sum := R.sum_ordered_link_corner_weights c covers_c
    (fun a => weight (a.1.val, a.2))
  have last_sum := S.sum_ordered_link_corner_weights d covers_d
    (fun b => weight (b.1.val, b.2))
  rw [← first_sum, ← last_sum]
  subst m
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun germ : C.Germ => weight germ.1) (points i i rfl)

open Classical in
/-- The actual intrinsic one-sided angles agree, including zero-curvature subdivisions. -/
theorem restricted_totalAngle_eq_of_terminal_germs (U V : Set Face)
    {leftRetain : Set (C.restrictFaces U).Seam}
    {rightRetain : Set (C.restrictFaces V).Seam}
    (p : (C.restrictFaces U).BoundaryEnd leftRetain)
    (q : (C.restrictFaces V).BoundaryEnd rightRetain)
    (initial : C.includeRestrictedGerm U p.val = C.includeRestrictedGerm V q.val)
    (terminal : C.includeRestrictedGerm U
        ((C.restrictFaces U).boundaryMate leftRetain p).val =
      C.includeRestrictedGerm V ((C.restrictFaces V).boundaryMate rightRetain q).val) :
    (C.restrictFaces U).totalAngle leftRetain
        ((C.restrictFaces U).boundaryEndVertex leftRetain p) =
      (C.restrictFaces V).totalAngle rightRetain
        ((C.restrictFaces V).boundaryEndVertex rightRetain q) :=
  C.sum_restricted_fan_weights_eq_of_terminal_germs U V p q initial terminal
    (fun a => (C.triangle a.1).cornerAngle a.2)

end Unfoldings.TriangleComplex
