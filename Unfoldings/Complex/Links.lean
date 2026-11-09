module

public import Unfoldings.Complex.Germs

/-!
# Pairing edge germs and restricting them to vertex links

Unpaired germs are fixed by seam transport. At every retained vertex class,
turning within corners and transporting across seams are involutions. Only
seam transport can have fixed points, precisely at boundary banks.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

theorem exists_germCrosses_iff (retain : Set C.Seam) (p : C.Germ) :
    (∃ q, C.GermCrosses retain p q) ↔ ¬ C.IsBoundaryEdge retain (C.germEdge p) := by
  constructor
  · rintro ⟨q, s, kept, side, b, hp, hq⟩ boundary
    have edge : C.germEdge p = C.seamSide s side := by rw [hp, C.germEdge_germOfEndpoint]
    apply boundary
    refine ⟨s, kept, ?_⟩
    cases side
    · exact Or.inl edge
    · exact Or.inr edge
  · intro attached
    by_contra none
    apply attached
    rintro ⟨s, kept, left | right⟩
    · have source : p = C.germOfEndpoint (C.seamSide s false) p.2 := by
        change p = C.germOfEndpoint (C.left s) p.2
        rw [← left, C.germOfEndpoint_germEdge]
      exact none ⟨_, s, kept, false, p.2, source, rfl⟩
    · have source : p = C.germOfEndpoint (C.seamSide s true) p.2 := by
        change p = C.germOfEndpoint (C.right s) p.2
        rw [← right, C.germOfEndpoint_germEdge]
      exact none ⟨_, s, kept, true, p.2, source, rfl⟩

/-- Transport across a retained seam, fixing a germ on an unpaired boundary bank. -/
def mateGerm (retain : Set C.Seam) (p : C.Germ) : C.Germ := by
  classical
  exact if paired : ∃ q, C.GermCrosses retain p q then Classical.choose paired else p

theorem mateGerm_of_crossing {retain : Set C.Seam} {p q : C.Germ}
    (crossing : C.GermCrosses retain p q) : C.mateGerm retain p = q := by
  classical
  have paired : ∃ q, C.GermCrosses retain p q := ⟨q, crossing⟩
  simp only [mateGerm, dite_eq_left paired]
  exact GermCrosses.unique C (Classical.choose_spec paired) crossing

theorem mateGerm_eq_self_iff (retain : Set C.Seam) (p : C.Germ) :
    C.mateGerm retain p = p ↔ C.IsBoundaryEdge retain (C.germEdge p) := by
  classical
  constructor
  · intro fixed
    by_contra attached
    obtain ⟨q, crossing⟩ := (C.exists_germCrosses_iff retain p).mpr attached
    rw [C.mateGerm_of_crossing crossing] at fixed
    exact GermCrosses.ne C crossing fixed.symm
  · intro boundary
    have none : ¬ ∃ q, C.GermCrosses retain p q := fun h =>
      ((C.exists_germCrosses_iff retain p).mp h) boundary
    simp only [mateGerm, dite_eq_right none]

theorem mateGerm_involutive (retain : Set C.Seam) : Function.Involutive (C.mateGerm retain) := by
  classical
  intro p
  by_cases paired : ∃ q, C.GermCrosses retain p q
  · obtain ⟨q, crossing⟩ := paired
    rw [C.mateGerm_of_crossing crossing, C.mateGerm_of_crossing crossing.symm]
  · have fixed : C.mateGerm retain p = p := by simp only [mateGerm, dite_eq_right paired]
    rw [fixed, fixed]

theorem mateGerm_vertex_eq (retain : Set C.Seam) (p : C.Germ) :
    C.vertexOfCorner retain (C.mateGerm retain p).1 = C.vertexOfCorner retain p.1 := by
  classical
  by_cases paired : ∃ q, C.GermCrosses retain p q
  · obtain ⟨q, crossing⟩ := paired
    rw [C.mateGerm_of_crossing crossing]
    exact crossing.vertex_eq.symm
  · simp only [mateGerm, dite_eq_right paired]

/-- The finite edge germs incident to one actual retained vertex copy. -/
def LinkGerm (retain : Set C.Seam) (v : C.Vertex retain) :=
  {p : C.Germ // C.vertexOfCorner retain p.1 = v}

instance (retain : Set C.Seam) (v : C.Vertex retain) : Finite (C.LinkGerm retain v) :=
  inferInstanceAs (Finite {p : C.Germ // C.vertexOfCorner retain p.1 = v})

instance (retain : Set C.Seam) (v : C.Vertex retain) : Fintype (C.LinkGerm retain v) :=
  Fintype.ofFinite _

theorem nonempty_linkGerm (retain : Set C.Seam) (v : C.Vertex retain) :
    Nonempty (C.LinkGerm retain v) := by
  obtain ⟨c, rfl⟩ := C.vertexOfCorner_surjective retain v
  exact ⟨⟨(c, false), rfl⟩⟩

/-- Turn to the other edge of the same corner, inside the chosen vertex link. -/
def linkTurn (retain : Set C.Seam) (v : C.Vertex retain) (p : C.LinkGerm retain v) :
    C.LinkGerm retain v := ⟨C.turnGerm p.val, p.property⟩

/-- Cross the paired seam or stop at a boundary, inside the chosen vertex link. -/
def linkMate (retain : Set C.Seam) (v : C.Vertex retain) (p : C.LinkGerm retain v) :
    C.LinkGerm retain v :=
  ⟨C.mateGerm retain p.val, (C.mateGerm_vertex_eq retain p.val).trans p.property⟩

theorem linkTurn_involutive (retain : Set C.Seam) (v : C.Vertex retain) :
    Function.Involutive (C.linkTurn retain v) := by
  intro p
  exact Subtype.ext (C.turnGerm_involutive p.val)

theorem linkTurn_ne (retain : Set C.Seam) (v : C.Vertex retain) (p : C.LinkGerm retain v) :
    C.linkTurn retain v p ≠ p := fun equal => C.turnGerm_ne p.val (congrArg Subtype.val equal)

theorem linkMate_involutive (retain : Set C.Seam) (v : C.Vertex retain) :
    Function.Involutive (C.linkMate retain v) := by
  intro p
  exact Subtype.ext (C.mateGerm_involutive retain p.val)

theorem linkMate_eq_self_iff (retain : Set C.Seam) (v : C.Vertex retain)
    (p : C.LinkGerm retain v) : C.linkMate retain v p = p ↔
      C.IsBoundaryEdge retain (C.germEdge p.val) := by
  rw [← C.mateGerm_eq_self_iff retain p.val]
  exact Subtype.ext_iff

theorem isBoundaryVertex_of_boundary_germ (retain : Set C.Seam) (p : C.Germ)
    (boundary : C.IsBoundaryEdge retain (C.germEdge p)) :
    C.IsBoundaryVertex retain (C.vertexOfCorner retain p.1) := by
  obtain ⟨⟨f, i⟩, b⟩ := p
  cases b
  · exact ⟨_, boundary, Or.inl rfl⟩
  · refine ⟨_, boundary, Or.inr ?_⟩
    fin_cases i <;> rfl

/-- A vertex meets the cut boundary exactly when its link has an unpaired germ. -/
theorem isBoundaryVertex_iff_linkMate_fixed (retain : Set C.Seam) (v : C.Vertex retain) :
    C.IsBoundaryVertex retain v ↔ ∃ p : C.LinkGerm retain v, C.linkMate retain v p = p := by
  constructor
  · rintro ⟨e, boundary, start | finish⟩
    · let p : C.LinkGerm retain v := ⟨C.germOfEndpoint e false, start.symm⟩
      refine ⟨p, (C.linkMate_eq_self_iff retain v p).mpr ?_⟩
      change C.IsBoundaryEdge retain (C.germEdge (C.germOfEndpoint e false))
      simpa only [C.germEdge_germOfEndpoint] using boundary
    · let p : C.LinkGerm retain v := ⟨C.germOfEndpoint e true, finish.symm⟩
      refine ⟨p, (C.linkMate_eq_self_iff retain v p).mpr ?_⟩
      change C.IsBoundaryEdge retain (C.germEdge (C.germOfEndpoint e true))
      simpa only [C.germEdge_germOfEndpoint] using boundary
  · rintro ⟨p, fixed⟩
    have boundary := C.isBoundaryVertex_of_boundary_germ retain p.val
      ((C.linkMate_eq_self_iff retain v p).mp fixed)
    rwa [p.property] at boundary

end Unfoldings.TriangleComplex
