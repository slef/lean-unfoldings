module

public import Unfoldings.Complex.GermEndpoints
public import Unfoldings.Geometry.EdgeParameters

/-! Actual local-edge endpoints in the orientation of each corner germ. -/

@[expose] public section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

theorem germ_apex_endpoint (p : C.Germ) :
    ((C.triangle p.1.1).endpoint (C.germEdge p).edge p.2).val =
      (C.triangle p.1.1).vertex p.1.2 := by
  obtain ⟨⟨face, i⟩, b⟩ := p
  cases b <;> fin_cases i <;> rfl

theorem germ_far_endpoint (p : C.Germ) :
    ((C.triangle p.1.1).endpoint (C.germEdge p).edge (!p.2)).val =
      (C.triangle p.1.1).vertex (C.germFarCorner p).2 := by
  obtain ⟨⟨face, i⟩, b⟩ := p
  cases b <;> fin_cases i <;> rfl

end Unfoldings.TriangleComplex
