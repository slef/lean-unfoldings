module

public import Unfoldings.Complex.FaceRestrictionVertices
public import Unfoldings.Complex.LinkOrdering

/-! Actual whole-face restriction link chains embed in their original corner link. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face) (U : Set Face)

open Classical in
def includeRestrictedGerm (p : (C.restrictFaces U).Germ) : C.Germ := ((p.1.1.val, p.1.2), p.2)

open Classical in
theorem includeRestrictedGerm_injective : Function.Injective (C.includeRestrictedGerm U) := by
  rintro ⟨⟨f, i⟩, b⟩ ⟨⟨g, j⟩, d⟩ same
  have faces : f = g := Subtype.ext (congrArg (fun p : C.Germ => p.1.1) same)
  have corners : i = j := congrArg (fun p : C.Germ => p.1.2) same
  have flags : b = d := congrArg (fun p : C.Germ => p.2) same
  subst g
  subst j
  subst d
  rfl

open Classical in
theorem includeRestrictedGerm_crossing {p q : (C.restrictFaces U).Germ}
    (crossing : (C.restrictFaces U).GermCrosses Set.univ p q) :
    C.GermCrosses Set.univ (C.includeRestrictedGerm U p) (C.includeRestrictedGerm U q) := by
  obtain ⟨s, _, side, b, rfl, rfl⟩ := crossing
  cases side
  · exact ⟨s.val, Set.mem_univ _, false, b, rfl, rfl⟩
  · exact ⟨s.val, Set.mem_univ _, true, b, rfl, rfl⟩

open Classical in
def includeRestrictedLinkGerm {w : (C.restrictFaces U).Vertex Set.univ}
    (p : (C.restrictFaces U).LinkGerm Set.univ w) :
    C.LinkGerm Set.univ (C.includeRestrictedVertexUniv U w) :=
  ⟨C.includeRestrictedGerm U p.val,
    congrArg (C.includeRestrictedVertexUniv U) p.property⟩

open Classical in
theorem includeRestrictedLinkGerm_injective (w : (C.restrictFaces U).Vertex Set.univ) :
    Function.Injective (C.includeRestrictedLinkGerm U (w := w)) := by
  intro p q same
  apply Subtype.ext
  exact C.includeRestrictedGerm_injective U (congrArg Subtype.val same)

open Classical in
/-- Retained corner order is inherited even when boundary copies split an original vertex. -/
def includeRestrictedLinkChain {w : (C.restrictFaces U).Vertex Set.univ} {n : ℕ}
    (c : ((C.restrictFaces U).linkSystem Set.univ w).Chain n) :
    (C.linkSystem Set.univ (C.includeRestrictedVertexUniv U w)).Chain n where
  point i := C.includeRestrictedLinkGerm U (c.point i)
  injective := (C.includeRestrictedLinkGerm_injective U w).comp c.injective
  disjoint i j same := c.disjoint i j ((C.includeRestrictedLinkGerm_injective U w) same)
  next := by
    intro i
    let R := C.restrictFaces U
    let source := R.turnGerm (c.point i.castSucc).val
    have joined : R.mateGerm Set.univ source = (c.point i.succ).val :=
      congrArg Subtype.val (c.next i)
    have paired : ∃ q, R.GermCrosses Set.univ source q := by
      by_contra none
      have fixed : R.mateGerm Set.univ source = source := by
        simp only [mateGerm, dite_eq_right none]
      have raw : (c.point i.succ).val = source := joined.symm.trans fixed
      exact c.disjoint i.succ i.castSucc (Subtype.ext raw)
    obtain ⟨q, crossing⟩ := paired
    have at_target : q = (c.point i.succ).val :=
      (R.mateGerm_of_crossing crossing).symm.trans joined
    have actual : R.GermCrosses Set.univ source (c.point i.succ).val := at_target ▸ crossing
    apply Subtype.ext
    exact C.mateGerm_of_crossing (C.includeRestrictedGerm_crossing U actual)

end Unfoldings.TriangleComplex
