module

public import Unfoldings.Development.AffineProjection

/-! An embedded affine projection gives an embedded development of its projected metric. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (A : Face → Plane ≃ᵃ[ℝ] Plane)
  (joined : ∀ s x, A (C.left s).face x.val = A (C.right s).face (C.identify s x).val)

@[simp] theorem affineProjectionTotal_inverse_apply
    (a : (C.affineProjectionComplex A joined).Total) :
    C.affineProjectionTotal A joined (C.affineProjectionInverseTotal A joined a) = a := by
  rcases a with ⟨f, x⟩
  refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
  exact (A f).apply_symm_apply x.val

/-- Projection injectivity is sufficient; the original metric need not be planar. -/
theorem affineProjectionDevelopment_injective
    (separated : Pairwise (fun f g =>
      Disjoint (interior (C.affineProjectedTriangle A f).carrier)
        (interior (C.affineProjectedTriangle A g).carrier)))
    (embedded : ∀ a b : C.Total, A a.1 a.2.val = A b.1 b.2.val →
      Relation.EqvGen (C.glue Set.univ) a b) :
    Function.Injective (C.affineProjectionDevelopment A joined separated).toPlane := by
  intro x y same
  let P := C.affineProjectionComplex A joined
  obtain ⟨a, rfl⟩ := MetricGluing.point_surjective P.Cell (P.glue Set.univ) x
  obtain ⟨b, rfl⟩ := MetricGluing.point_surjective P.Cell (P.glue Set.univ) y
  change a.2.val = b.2.val at same
  have equal : A (C.affineProjectionInverseTotal A joined a).1
      (C.affineProjectionInverseTotal A joined a).2.val =
        A (C.affineProjectionInverseTotal A joined b).1
          (C.affineProjectionInverseTotal A joined b).2.val := by
    change A a.1 ((A a.1).symm a.2.val) = A b.1 ((A b.1).symm b.2.val)
    simpa only [AffineEquiv.apply_symm_apply] using same
  apply (P.point_eq_iff Set.univ a b).mpr
  change Relation.EqvGen ((C.affineProjectionComplex A joined).glue Set.univ) a b
  have related := C.affineProjection_eqvGen A joined Set.univ
    (embedded _ _ equal)
  rw [C.affineProjectionTotal_inverse_apply A joined a,
    C.affineProjectionTotal_inverse_apply A joined b] at related
  exact related

/-- Identity projected placements cover exactly the union of their actual triangles. -/
theorem affineProjectionDevelopment_range
    (separated : Pairwise (fun f g =>
      Disjoint (interior (C.affineProjectedTriangle A f).carrier)
        (interior (C.affineProjectedTriangle A g).carrier))) :
    Set.range (C.affineProjectionDevelopment A joined separated).toPlane =
      ⋃ f, (C.affineProjectedTriangle A f).carrier := by
  let P := C.affineProjectionComplex A joined
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨⟨f, y⟩, rfl⟩ := MetricGluing.point_surjective P.Cell (P.glue Set.univ) x
    exact Set.mem_iUnion.mpr ⟨f, y.property⟩
  · intro member
    obtain ⟨f, inside⟩ := Set.mem_iUnion.mp member
    exact ⟨P.faceMap Set.univ f ⟨p, inside⟩, rfl⟩

end Unfoldings.TriangleComplex
