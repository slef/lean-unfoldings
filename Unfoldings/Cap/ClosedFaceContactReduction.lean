module

public import Unfoldings.Cap.ClosedFaceCircleContact
public import Unfoldings.Geometry.FiniteRadiusContact

/-! Nontrivial closed-face contact sets identify physical points even at exceptional radii. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)
  {U : Set Plane} (convex : Convex ℝ U) (center : Plane)
  {exception : Set ℝ} (finite : exception.Finite)
  (contacts : ∀ f g (p q : Plane),
    p ∈ (K.projectedTriangle f).carrier ∩ U →
    q ∈ (K.projectedTriangle g).carrier ∩ U →
    0 < ‖D.projectedPlacement K f p - center‖ →
    ‖D.projectedPlacement K f p - center‖ ∉ exception →
    D.projectedPlacement K f p = D.projectedPlacement K g q → p = q)

include convex finite contacts in
/-- A segment of actual closed-face contact has the same physical preimage throughout.
The conclusion includes exceptional radii and the developed center. -/
theorem projected_preimages_eq_of_nontrivial_contact (f g : Face)
    (nontrivial :
      (D.projectedPlacement K f '' ((K.projectedTriangle f).carrier ∩ U) ∩
        D.projectedPlacement K g '' ((K.projectedTriangle g).carrier ∩ U)).Nontrivial)
    {p q : Plane} (first : p ∈ (K.projectedTriangle f).carrier ∩ U)
    (last : q ∈ (K.projectedTriangle g).carrier ∩ U)
    (same : D.projectedPlacement K f p = D.projectedPlacement K g q) : p = q := by
  let A := D.projectedPlacement K f '' ((K.projectedTriangle f).carrier ∩ U) ∩
    D.projectedPlacement K g '' ((K.projectedTriangle g).carrier ∩ U)
  have convex_A : Convex ℝ A :=
    (((K.projectedTriangle f).convex_carrier.inter convex).affine_image
      (D.projectedPlacement K f).toAffineMap).inter
        (((K.projectedTriangle g).convex_carrier.inter convex).affine_image
          (D.projectedPlacement K g).toAffineMap)
  have agree : Set.EqOn (D.projectedPlacement K f).symm (D.projectedPlacement K g).symm A := by
    apply eqOn_convex_of_finite_radius_exceptions convex_A nontrivial
      (D.projectedPlacement K f).symm.toContinuousAffineEquiv.toHomeomorph.continuous
      (D.projectedPlacement K g).symm.toContinuousAffineEquiv.toHomeomorph.continuous
      center (finite.insert 0)
    rintro z ⟨⟨a, first, rfl⟩, ⟨b, last, equal⟩⟩ outside
    have outside_zero : ‖D.projectedPlacement K f a - center‖ ≠ 0 :=
      fun zero => outside (Or.inl zero)
    have same_point := contacts f g a b first last
      (lt_of_le_of_ne (norm_nonneg _) outside_zero.symm)
      (fun member => outside (Or.inr member)) equal.symm
    change (D.projectedPlacement K f).symm (D.projectedPlacement K f a) =
      (D.projectedPlacement K g).symm (D.projectedPlacement K f a)
    rw [AffineEquiv.symm_apply_apply, ← equal, AffineEquiv.symm_apply_apply]
    exact same_point
  have equal := agree ⟨⟨p, first, rfl⟩, ⟨q, last, same.symm⟩⟩
  rw [same, AffineEquiv.symm_apply_apply] at equal
  rw [← same, AffineEquiv.symm_apply_apply] at equal
  exact equal

include convex finite contacts in
/-- Any contact between different physical points is isolated for its pair of actual faces. -/
theorem projected_contact_eq_singleton_of_ne (f g : Face)
    {p q : Plane} (first : p ∈ (K.projectedTriangle f).carrier ∩ U)
    (last : q ∈ (K.projectedTriangle g).carrier ∩ U)
    (different : p ≠ q)
    (same : D.projectedPlacement K f p = D.projectedPlacement K g q) :
    D.projectedPlacement K f '' ((K.projectedTriangle f).carrier ∩ U) ∩
      D.projectedPlacement K g '' ((K.projectedTriangle g).carrier ∩ U) =
        {D.projectedPlacement K f p} := by
  apply Set.Subsingleton.eq_singleton_of_mem
  · apply Set.not_nontrivial_iff.mp
    intro nontrivial
    exact different (D.projected_preimages_eq_of_nontrivial_contact K convex center finite
      contacts f g nontrivial first last same)
  · exact ⟨⟨p, first, rfl⟩, ⟨q, last, same.symm⟩⟩

include convex finite contacts in
/-- Finitely many exceptional circles leave only finitely many foreign physical contact points. -/
theorem finite_foreign_projected_contacts :
    {z : Plane | ∃ f g : Face, ∃ p q : Plane,
      p ∈ (K.projectedTriangle f).carrier ∩ U ∧
      q ∈ (K.projectedTriangle g).carrier ∩ U ∧ p ≠ q ∧
      D.projectedPlacement K f p = z ∧ D.projectedPlacement K g q = z}.Finite := by
  let bad := fun f g : Face => {z : Plane | ∃ p q : Plane,
    p ∈ (K.projectedTriangle f).carrier ∩ U ∧
    q ∈ (K.projectedTriangle g).carrier ∩ U ∧ p ≠ q ∧
    D.projectedPlacement K f p = z ∧ D.projectedPlacement K g q = z}
  have pair_finite (f g : Face) : (bad f g).Finite := by
    by_cases nonempty : (bad f g).Nonempty
    · obtain ⟨z, p, q, first, last, different, first_value, last_value⟩ := nonempty
      have singleton := D.projected_contact_eq_singleton_of_ne K convex center finite contacts
        f g first last different (first_value.trans last_value.symm)
      apply (Set.finite_singleton z).subset
      rintro w ⟨a, b, first, last, _, a_value, b_value⟩
      rw [← first_value, ← singleton]
      exact ⟨⟨a, first, a_value⟩, ⟨b, last, b_value⟩⟩
    · exact Set.finite_empty.subset (Set.not_nonempty_iff_eq_empty.mp nonempty).subset
  apply (Set.finite_iUnion fun f => Set.finite_iUnion fun g => pair_finite f g).subset
  rintro z ⟨f, g, witness⟩
  exact Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨g, witness⟩⟩

end Unfoldings.FacewiseDevelopment
