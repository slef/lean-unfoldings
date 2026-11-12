module

public import Unfoldings.Cap.ClosedFaceContactReduction
public import Unfoldings.Geometry.NonvertexTriangleContact

/-! Foreign closed-face contacts involve an actual corner, with no radius exclusions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

/-- A finite-radius contact theorem rules out every foreign contact between nonvertex points.
Only contacts involving actual face corners remain, including on exceptional circles. -/
theorem isVertex_or_isVertex_of_foreign_projected_contact
    {U : Set Plane} (opened : IsOpen U) (convex : Convex ℝ U) (center : Plane)
    {exception : Set ℝ} (finite : exception.Finite)
    (contacts : ∀ f g (p q : Plane),
      p ∈ (K.projectedTriangle f).carrier ∩ U →
      q ∈ (K.projectedTriangle g).carrier ∩ U →
      0 < ‖D.projectedPlacement K f p - center‖ →
      ‖D.projectedPlacement K f p - center‖ ∉ exception →
      D.projectedPlacement K f p = D.projectedPlacement K g q → p = q)
    (f g : Face) {p q : Plane}
    (first : p ∈ (K.projectedTriangle f).carrier ∩ U)
    (last : q ∈ (K.projectedTriangle g).carrier ∩ U)
    (different : p ≠ q)
    (same : D.projectedPlacement K f p = D.projectedPlacement K g q) :
    (K.projectedTriangle f).IsVertex p ∨ (K.projectedTriangle g).IsVertex q := by
  let A := D.projectedPlacement K f
  let B := D.projectedPlacement K g
  let T := (K.projectedTriangle f).affineImage A.toAffineMap A.injective
  let S := (K.projectedTriangle g).affineImage B.toAffineMap B.injective
  let V := A.symm ⁻¹' U ∩ B.symm ⁻¹' U
  have V_open : IsOpen V :=
    (opened.preimage A.symm.toContinuousAffineEquiv.toHomeomorph.continuous).inter
      (opened.preimage B.symm.toContinuousAffineEquiv.toHomeomorph.continuous)
  have contact : A p ∈ T.carrier ∩ S.carrier ∩ V := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [(K.projectedTriangle f).affineImage_carrier A.toAffineMap A.injective]
      exact Set.mem_image_of_mem A first.1
    · rw [show S.carrier = B '' (K.projectedTriangle g).carrier from
        (K.projectedTriangle g).affineImage_carrier B.toAffineMap B.injective]
      exact ⟨q, last.1, same.symm⟩
    · change A.symm (A p) ∈ U ∧ B.symm (A p) ∈ U
      rw [A.symm_apply_apply, same, B.symm_apply_apply]
      exact ⟨first.2, last.2⟩
  have singleton := D.projected_contact_eq_singleton_of_ne K convex center finite contacts
    f g first last different same
  have isolated : ∀ z ∈ T.carrier ∩ S.carrier ∩ V, z = A p := by
    rintro z ⟨⟨in_T, in_S⟩, in_V⟩
    obtain ⟨a, member_a, value_a⟩ :=
      ((K.projectedTriangle f).affineImage_carrier A.toAffineMap A.injective).subset in_T
    obtain ⟨b, member_b, value_b⟩ :=
      ((K.projectedTriangle g).affineImage_carrier B.toAffineMap B.injective).subset in_S
    change A a = z at value_a
    change B b = z at value_b
    have physical_a : a ∈ U := by
      have actual : A.symm z ∈ U := in_V.1
      rw [← value_a, A.symm_apply_apply] at actual
      exact actual
    have physical_b : b ∈ U := by
      have actual : B.symm z ∈ U := in_V.2
      rw [← value_b, B.symm_apply_apply] at actual
      exact actual
    have in_intersection : z ∈
        D.projectedPlacement K f '' ((K.projectedTriangle f).carrier ∩ U) ∩
          D.projectedPlacement K g '' ((K.projectedTriangle g).carrier ∩ U) :=
      ⟨⟨a, ⟨member_a, physical_a⟩, value_a⟩, ⟨b, ⟨member_b, physical_b⟩, value_b⟩⟩
    exact Set.mem_singleton_iff.mp (singleton ▸ in_intersection)
  rcases T.isVertex_or_isVertex_of_isolated_contact S contact.1.1 contact.1.2 V_open
      contact.2 isolated with ⟨i, corner⟩ | ⟨i, corner⟩
  · exact Or.inl ⟨i, A.injective corner⟩
  · exact Or.inr ⟨i, B.injective (corner.trans same)⟩

end Unfoldings.FacewiseDevelopment
