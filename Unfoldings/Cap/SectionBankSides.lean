module

public import Unfoldings.Cap.ProjectedContourSides
public import Unfoldings.Cap.GermVectors
public import Unfoldings.Cap.SectionTrace
public import Unfoldings.Geometry.LineCrossingSides

/-! Actual section crossing signs from the oriented original bank face. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Every point of a raw projected bank lies on its directed germ line. -/
theorem projectedGerm_bank_height_zero (p : C.Germ) {z : Plane}
    (member : z ∈ (K.projectedTriangle p.1.1).edge (C.germEdge p).edge) :
    orient (K.projectFace p.1.1 ((C.triangle p.1.1).vertex p.1.2))
      (K.projectFace p.1.1 ((C.triangle p.1.1).vertex (C.germFarCorner p).2)) z = 0 := by
  obtain ⟨⟨f, i⟩, side⟩ := p
  cases side
  · exact orient_eq_zero_of_mem_segment member
  · have zero := orient_eq_zero_of_mem_segment member
    change orient ((K.projectedTriangle f).vertex (Triangle.next (Triangle.next i)))
      ((K.projectedTriangle f).vertex (Triangle.next (Triangle.next (Triangle.next i)))) z = 0
      at zero
    rw [Triangle.next_next_next] at zero
    change orient ((K.projectedTriangle f).vertex i)
      ((K.projectedTriangle f).vertex (Triangle.next (Triangle.next i))) z = 0
    rw [orient_swap, zero, neg_zero]

/-- A regular section leaving the original face across its positive bank has negative bank cross. -/
theorem projectedGerm_section_exit_sign (p : C.Germ)
    (positive : 0 < K.projectedGermOrientation p) {a b : Plane} (different : a ≠ b)
    (regular : ∀ t : ℝ, AffineMap.lineMap a b t ≠ (K.projectedTriangle p.1.1).vertex p.1.2)
    {s t : ℝ} (before : s < t)
    (first : AffineMap.lineMap a b s ∈ (K.projectedTriangle p.1.1).carrier)
    (crossing : AffineMap.lineMap a b t ∈
      (K.projectedTriangle p.1.1).edge (C.germEdge p).edge) :
    orient 0 (K.projectedGermVector p) (b - a) < 0 := by
  have genuine : K.projectFace p.1.1 ((C.triangle p.1.1).vertex p.1.2) ≠
      K.projectFace p.1.1 ((C.triangle p.1.1).vertex (C.germFarCorner p).2) := by
    intro equal
    have corners := (C.triangle p.1.1).vertex_injective ((K.projectFace_injective p.1.1) equal)
    exact C.germFarCorner_ne p (Prod.ext rfl corners.symm)
  have meets := K.projectedGerm_bank_height_zero p crossing
  exact line_exit_left_sign before meets (K.projectedGerm_side_nonneg p positive first)
    (line_transverse_of_avoids_endpoint genuine different regular t meets)

namespace SectionFaceTrace

variable {K} {a b : Plane} (T : K.SectionFaceTrace a b)

/-- The actual first face and actual bank intersection determine the transverse crossing sign. -/
theorem bank_exit_sign (different : a ≠ b)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap a b t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) (p : C.Germ) (first_face : T.face i.castSucc = p.1.1)
    (positive : 0 < K.projectedGermOrientation p)
    (crossing : T.point i.castSucc.succ ∈
      (K.projectedTriangle p.1.1).edge (C.germEdge p).edge) :
    orient 0 (K.projectedGermVector p) (b - a) < 0 := by
  have member := T.point_mem_face_first i.castSucc
  rw [first_face] at member
  exact K.projectedGerm_section_exit_sign p positive different
    (fun t => regular t _ _) (T.increasing Fin.castSucc_lt_succ) member crossing

end SectionFaceTrace
end Unfoldings.ConvexCap
