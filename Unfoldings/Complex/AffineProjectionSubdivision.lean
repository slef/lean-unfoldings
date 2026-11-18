module

public import Unfoldings.Complex.Subdivision
public import Unfoldings.Development.AffineProjectionEmbedding

/-! Compatible physical projections give actual conforming subdivisions in the projected metric. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex.Subdivision

universe u v w z

variable {Face : Type u} [Fintype Face] {Child : Type w} [Fintype Child]
  {C : TriangleComplex.{u, v} Face} {D : TriangleComplex.{w, z} Child} (S : C.Subdivision D)
  (A : Face → Plane ≃ᵃ[ℝ] Plane)
  (joinedA : ∀ s x, A (C.left s).face x.val = A (C.right s).face (C.identify s x).val)
  (B : Child → Plane ≃ᵃ[ℝ] Plane)
  (joinedB : ∀ s x, B (D.left s).face x.val = B (D.right s).face (D.identify s x).val)
  (compatible : ∀ g x, A (S.parent g) (S.place g x) = B g x)

/-- In the projected metric each fine triangle is literally a subset of its old triangle. -/
def affineProjectionSubdivision :
    (C.affineProjectionComplex A joinedA).Subdivision
      (D.affineProjectionComplex B joinedB) where
  parent := S.parent
  place _ := AffineIsometryEquiv.refl ℝ Plane
  inside g p member := by
    obtain ⟨x, inside, equal⟩ := ((D.triangle g).affineImage_carrier
      (B g).toAffineMap (B g).injective).subset member
    exact ((C.triangle (S.parent g)).affineImage_carrier
      (A (S.parent g)).toAffineMap (A (S.parent g)).injective).symm.subset
        ⟨S.place g x, S.inside g x inside, (compatible g x).trans equal⟩
  cover f x := by
    let old := C.affineProjectionInverseTotal A joinedA ⟨f, x⟩
    obtain ⟨g, y, parent, equal⟩ := S.cover f old.2
    subst f
    refine ⟨g, (D.affineProjectionTotal B joinedB ⟨g, y⟩).2, rfl, ?_⟩
    change B g y.val = x.val
    calc
      _ = A (S.parent g) (S.place g y.val) := (compatible g y.val).symm
      _ = A (S.parent g) old.2.val := congrArg (A (S.parent g)) equal
      _ = x.val := (A (S.parent g)).apply_symm_apply x.val

theorem affineProjectionSubdivision_parentPoint (a : D.Total) :
    (S.affineProjectionSubdivision A joinedA B joinedB compatible).parentPoint
      (D.affineProjectionTotal B joinedB a) =
        C.affineProjectionTotal A joinedA (S.parentPoint a) := by
  rcases a with ⟨g, x⟩
  refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
  exact (compatible g x.val).symm

theorem affineProjectionSubdivision_parent_inverse
    (a : (D.affineProjectionComplex B joinedB).Total) :
    C.affineProjectionTotal A joinedA
        (S.parentPoint (D.affineProjectionInverseTotal B joinedB a)) =
      (S.affineProjectionSubdivision A joinedA B joinedB compatible).parentPoint a := by
  have equal := S.affineProjectionSubdivision_parentPoint A joinedA B joinedB compatible
    (D.affineProjectionInverseTotal B joinedB a)
  rw [D.affineProjectionTotal_inverse_apply B joinedB a] at equal
  exact equal.symm

/-- Actual retained seam correspondence survives the change to the projected metric. -/
theorem affineProjectionSubdivision_conforming {retain : Set C.Seam}
    {fineRetain : Set D.Seam} (H : S.Conforming retain fineRetain) :
    (S.affineProjectionSubdivision A joinedA B joinedB compatible).Conforming
      retain fineRetain := by
  constructor
  · intro a b step
    have old := D.affineProjection_inverse_glue B joinedB fineRetain step
    have related := C.affineProjection_eqvGen A joinedA retain (H.respects _ _ old)
    rw [S.affineProjectionSubdivision_parent_inverse A joinedA B joinedB compatible a,
      S.affineProjectionSubdivision_parent_inverse A joinedA B joinedB compatible b] at related
    exact related
  · intro a b related
    have old := C.affineProjection_inverse_eqvGen A joinedA retain related
    have parent (x : (D.affineProjectionComplex B joinedB).Total) :
        C.affineProjectionInverseTotal A joinedA
            ((S.affineProjectionSubdivision A joinedA B joinedB compatible).parentPoint x) =
          S.parentPoint (D.affineProjectionInverseTotal B joinedB x) := by
      rw [← S.affineProjectionSubdivision_parent_inverse A joinedA B joinedB compatible x,
        C.affineProjectionInverseTotal_apply A joinedA]
    rw [parent a, parent b] at old
    have lifted := D.affineProjection_eqvGen B joinedB fineRetain (H.lifts _ _ old)
    rw [D.affineProjectionTotal_inverse_apply B joinedB a,
      D.affineProjectionTotal_inverse_apply B joinedB b] at lifted
    exact lifted

end Unfoldings.TriangleComplex.Subdivision
