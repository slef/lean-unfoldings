module

public import Unfoldings.Complex.Germs

/-!
# The far endpoints of actual corner germs

A germ starts at one triangle corner and follows one incident edge. Its far
corner is the other endpoint of that same edge. Actual seam endpoint
permutations commute with exchanging the two endpoints.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

def germFarCorner (p : C.Germ) : C.Corner :=
  (p.1.1, if p.2 then Triangle.next (Triangle.next p.1.2) else Triangle.next p.1.2)

theorem germ_eq_of_corner_edge {p q : C.Germ} (corner : p.1 = q.1)
    (edge : C.germEdge p = C.germEdge q) : p = q := by
  obtain ⟨c, b⟩ := p
  obtain ⟨d, e⟩ := q
  change c = d at corner
  subst d
  obtain ⟨face, i⟩ := c
  cases b <;> cases e <;> fin_cases i <;> simp_all [germEdge, Triangle.next]

theorem germFarCorner_ne (p : C.Germ) : C.germFarCorner p ≠ p.1 := by
  obtain ⟨⟨face, i⟩, side⟩ := p
  cases side <;> fin_cases i <;> simp [germFarCorner, Triangle.next]

theorem germFarCorner_germOfEndpoint (e : EdgeRef Face) (b : Bool) :
    C.germFarCorner (C.germOfEndpoint e b) = (C.germOfEndpoint e (!b)).1 := by
  obtain ⟨face, i⟩ := e
  cases b <;> fin_cases i <;> rfl

theorem acrossEndpoint_not (s : C.Seam) (side b : Bool) :
    C.acrossEndpoint s side (!b) = !(C.acrossEndpoint s side b) := by
  have different := (C.acrossEndpoint s side).injective.ne (Bool.not_ne_self b)
  cases first : C.acrossEndpoint s side b <;>
    cases last : C.acrossEndpoint s side (!b) <;> simp_all

end Unfoldings.TriangleComplex
