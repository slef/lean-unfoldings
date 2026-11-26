module

public import Unfoldings.Roof.SignedClosingHinge
public import Unfoldings.Roof.SharpClosingContacts

/-! A regular bank contact gives its earlier and later active normals and its signed turn. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Real InnerProductGeometry Cap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {U : Set Face} {origin : Plane} {I : Type*}

local notation "east" => (WithLp.toLp 2 ![(1 : ℝ), 0] : Plane)

namespace RegularClosingLink

variable (L : K.RegularClosingLink U origin east I)

open Classical in
/-- The face carrying the incoming half of the forward closing link. -/
def earlierFace (i : I) : Face := L.contactFace i (decide (0 < L.outgoing i))

open Classical in
/-- The face carrying the outgoing half of the forward closing link. -/
def laterFace (i : I) : Face := L.contactFace i (!decide (0 < L.outgoing i))

private theorem join_above {z : Plane} (above : 0 ≤ z 1) (nonzero : orient 0 z east ≠ 0) :
    0 < z 1 := by
  by_contra! h
  have eq : z 1 = 0 := above.antisymm' h
  apply nonzero
  have east1 : (![1, 0] : Fin 2 → ℝ) 1 = 0 := rfl
  simp only [orient, PiLp.zero_apply, sub_zero, east1, eq, mul_zero, zero_mul]

open Classical in
/-- The regular horizontal closing contact contributes the hinge angle change
from the earlier active normal to the later one. Flat contacts contribute zero. -/
theorem exists_signed_horizontal_turn (i : I)
    (above : ∀ g : C.LinkGerm Set.univ
      (C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ (L.bank i))),
      g.val.1.1 ∈ U → 0 ≤ K.projectedGermRay g 1) :
    let p := K.normalSlope (L.earlierFace i)
    let q := K.normalSlope (L.laterFace i)
    ∃ m b : ℝ, p 1 = m * p 0 + b ∧ q 1 = m * q 0 + b ∧
      K.restrictedBoundaryTurnError U (L.bank i) = hingeAngleChange m b (p 0) (q 0) := by
  let R := C.restrictFaces U
  let e := L.bank i
  let w := C.includeRestrictedVertexUniv U (R.boundaryEndVertex Set.univ e)
  have position : K.projectedVertex w = origin + L.time i • east := by
    change K.projectedVertex (C.vertexOfCorner Set.univ (e.val.1.1.val, e.val.1.2)) = _
    rw [K.projectedVertex_ofCorner]
    have h := L.position i
    rw [(K.folding.restrictFaces U).boundaryPosition_raw] at h
    exact h
  have inside := (K.projectedVertex_mem_interior_iff w).mp (position ▸ L.inside i)
  obtain ⟨a, b, slopes, transverse⟩ := L.regular i
  let l := L.contactFace i false
  let r := L.contactFace i true
  have flat {f g : Face} (h : K.normalSlope f = K.normalSlope g)
      (zero : K.restrictedBoundaryTurnError U e = 0) :
      ∃ m b, K.normalSlope f 1 = m * K.normalSlope f 0 + b ∧
        K.normalSlope g 1 = m * K.normalSlope g 0 + b ∧
        K.restrictedBoundaryTurnError U e =
          hingeAngleChange m b (K.normalSlope f 0) (K.normalSlope g 0) := by
    refine ⟨0, K.normalSlope g 1, ?_, ?_, ?_⟩
    · rw [h, zero_mul, zero_add]
    · rw [zero_mul, zero_add]
    · rw [zero, h, hingeAngleChange, sub_self]
  rcases mul_neg_iff.mp (L.opposite i) with ⟨out, incoming⟩ | ⟨out, incoming⟩
  · simp only [earlierFace, laterFace, decide_eq_true out, Bool.not_true]
    have last : Cap.horizontal ((K.folding.restrictFaces U).germDirection
          (R.boundaryMate Set.univ e).val) = (-L.incoming i) • (-east) := by
      rw [neg_smul, smul_neg, neg_neg]
      exact L.incoming_ray i
    rcases K.restrictedBoundaryTurnError_eq_hinge_difference U e east a b inside slopes transverse
      out (neg_pos.mpr incoming) (L.outgoing_ray i) last with h | ⟨g, member, tie, cross, eq⟩
    · exact flat h.1.symm h.2
    · let join := K.projectedGermRay g
      have jp := join_above (above g member) cross
      obtain ⟨first, second, turn⟩ := K.signed_horizontal_sectionHinge l r join jp tie
      exact ⟨_, _, first, second, eq.trans turn⟩
  · have out_not : ¬0 < L.outgoing i := not_lt_of_ge out.le
    simp only [earlierFace, laterFace, decide_eq_false_iff_not.mpr out_not, Bool.not_false]
    have first : Cap.horizontal ((K.folding.restrictFaces U).germDirection e.val) =
        (-L.outgoing i) • (-east) := by
      rw [neg_smul, smul_neg, neg_neg]
      exact L.outgoing_ray i
    have last : Cap.horizontal ((K.folding.restrictFaces U).germDirection
          (R.boundaryMate Set.univ e).val) = L.incoming i • (-(-east)) := by
      rw [neg_neg]
      exact L.incoming_ray i
    have tr : a = b ∨ inner ℝ (a - b) (-east) ≠ 0 := by
      rw [inner_neg_right, neg_ne_zero]
      exact transverse
    rcases K.restrictedBoundaryTurnError_eq_hinge_difference U e (-east) a b inside slopes tr
      (neg_pos.mpr out) incoming first last with h | ⟨g, member, tie, cross, eq⟩
    · exact flat h.1 h.2
    · let join := K.projectedGermRay g
      have jp : 0 < join 1 := by
        by_contra! h
        have zero : join 1 = 0 := (above g member).antisymm' h
        apply cross
        change orient 0 join (-east) = 0
        have east1 : (-east : Plane) 1 = 0 := by simp
        simp only [orient, PiLp.zero_apply, sub_zero, east1, zero, mul_zero, zero_mul]
      change inner ℝ (K.normalSlope l - K.normalSlope r) join = 0 at tie
      have reverse_tie : inner ℝ (K.normalSlope r - K.normalSlope l) join = 0 := by
        rw [show K.normalSlope r - K.normalSlope l = -(K.normalSlope l - K.normalSlope r) by abel,
          inner_neg_left, tie, neg_zero]
      obtain ⟨first, second, turn⟩ := K.signed_horizontal_sectionHinge r l join jp reverse_tie
      have eq' : K.sectionDirection l join = K.sectionDirection r join := by
        change inner ℝ (K.normalSlope l - K.normalSlope r) join = 0 at tie
        rw [inner_sub_left, sub_eq_zero] at tie
        simp only [sectionDirection, tie]
      change K.restrictedBoundaryTurnError U e =
        angle (K.sectionDirection l join) (K.sectionDirection r (-east)) -
          angle (K.sectionDirection l join) (K.sectionDirection l (-east)) at eq
      rw [sectionDirection_neg, sectionDirection_neg, angle_neg_right, angle_neg_right] at eq
      refine ⟨_, _, first, second, eq.trans ?_⟩
      rw [← turn, eq']
      ring

end RegularClosingLink
end Unfoldings.ConvexRoof
