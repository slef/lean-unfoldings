module

public import Unfoldings.Cone.Tangent

/-! Link connectivity identifies all actual wedge apices in the tangent fan. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

def tangentGermApex (p : C.LinkGerm retain v) : C.TangentFan retain v :=
  C.tangentFaceMap retain v ⟨p.val.1, p.property⟩
    (C.tangentApex retain v ⟨p.val.1, p.property⟩)

@[simp] theorem tangentGermApex_turn (p : C.LinkGerm retain v) :
    C.tangentGermApex retain v (C.linkTurn retain v p) = C.tangentGermApex retain v p := rfl

theorem tangentGermApex_eq_of_crossing (p q : C.LinkGerm retain v)
    (crossing : C.GermCrosses retain p.val q.val) :
    C.tangentGermApex retain v p = C.tangentGermApex retain v q := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  obtain ⟨s, kept, side, b, rfl, rfl⟩ := crossing
  let seam : C.TangentSeam retain v := ⟨(s, side, b), kept, hp⟩
  exact C.tangentSeam_apex_eq retain v seam

theorem tangentGermApex_mate (p : C.LinkGerm retain v) :
    C.tangentGermApex retain v (C.linkMate retain v p) = C.tangentGermApex retain v p := by
  classical
  by_cases paired : ∃ q, C.GermCrosses retain p.val q
  · obtain ⟨q, crossing⟩ := paired
    have crossed : C.GermCrosses retain p.val (C.linkMate retain v p).val := by
      change C.GermCrosses retain p.val (C.mateGerm retain p.val)
      rw [C.mateGerm_of_crossing crossing]
      exact crossing
    exact (C.tangentGermApex_eq_of_crossing retain v p _ crossed).symm
  · have fixed : C.linkMate retain v p = p := by
      apply Subtype.ext
      simp only [linkMate, mateGerm, dite_eq_right paired]
    rw [fixed]

theorem tangentGermApex_eq (p q : C.LinkGerm retain v) :
    C.tangentGermApex retain v p = C.tangentGermApex retain v q := by
  have related := C.linkGerms_related retain v p q
  induction related with
  | rel p q step =>
    rcases step with rfl | rfl
    · exact (C.tangentGermApex_turn retain v p).symm
    · exact (C.tangentGermApex_mate retain v p).symm
  | refl p => rfl
  | symm p q h ih => exact ih.symm
  | trans p q r hpq hqr ih₁ ih₂ => exact ih₁.trans ih₂

/-- All wedge centers agree because their original corner link is connected. -/
theorem tangentApex_eq (c d : C.CornerAt retain v) :
    C.tangentFaceMap retain v c (C.tangentApex retain v c) =
      C.tangentFaceMap retain v d (C.tangentApex retain v d) :=
  C.tangentGermApex_eq retain v ⟨(c.val, false), c.property⟩ ⟨(d.val, false), d.property⟩

/-- Choose the common origin only after proving all original apex images agree. -/
def tangentOrigin : C.TangentFan retain v :=
  C.tangentGermApex retain v (Classical.choice (C.nonempty_linkGerm retain v))

theorem tangentOrigin_eq (c : C.CornerAt retain v) :
    C.tangentOrigin retain v = C.tangentFaceMap retain v c (C.tangentApex retain v c) :=
  C.tangentGermApex_eq retain v _ ⟨(c.val, false), c.property⟩

instance : Inhabited (C.TangentFan retain v) := ⟨C.tangentOrigin retain v⟩

end Unfoldings.TriangleComplex
