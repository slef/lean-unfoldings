module

public import Unfoldings.Complex.AffineProjectionSubdivision
public import Unfoldings.Complex.SubdivisionCornerAngles
public import Unfoldings.Complex.AffineProjectionAngles
public import Unfoldings.Development.AffineProjectionEmbedding

/-! Projected subdivisions preserve the actual corresponding retained vertex copies. -/

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

/-- The same actual vertex copies correspond before and after changing the face metric. -/
theorem affineProjectionSubdivision_vertexPoint {retain : Set C.Seam}
    {fineRetain : Set D.Seam} (H : S.Conforming retain fineRetain)
    (fine : D.Vertex fineRetain) (coarse : C.Vertex retain)
    (same : H.metricEquiv (D.vertexPoint fineRetain fine) = C.vertexPoint retain coarse) :
    (S.affineProjectionSubdivision_conforming A joinedA B joinedB compatible H).metricEquiv
      ((D.affineProjectionComplex B joinedB).vertexPoint fineRetain
        (D.affineProjectionVertexEquiv B joinedB fineRetain fine)) =
      (C.affineProjectionComplex A joinedA).vertexPoint retain
        (C.affineProjectionVertexEquiv A joinedA retain coarse) := by
  obtain ⟨c, rfl⟩ := C.vertexOfCorner_surjective retain coarse
  obtain ⟨d, rfl⟩ := D.vertexOfCorner_surjective fineRetain fine
  let HP := S.affineProjectionSubdivision_conforming A joinedA B joinedB compatible H
  have old : Relation.EqvGen (C.glue retain)
      (S.parentPoint (D.cornerPoint d)) (C.cornerPoint c) :=
    (C.point_eq_iff retain _ _).mp same
  have related := C.affineProjection_eqvGen A joinedA retain old
  change HP.metricEquiv ((D.affineProjectionComplex B joinedB).faceMap fineRetain d.1
    ((D.affineProjectionComplex B joinedB).cornerPoint d).2) = _
  refine (HP.metricEquiv_faceMap d.1
    ((D.affineProjectionComplex B joinedB).cornerPoint d).2).trans ?_
  apply ((C.affineProjectionComplex A joinedA).point_eq_iff retain _ _).mpr
  change Relation.EqvGen ((C.affineProjectionComplex A joinedA).glue retain)
    ((S.affineProjectionSubdivision A joinedA B joinedB compatible).parentPoint
      (D.affineProjectionTotal B joinedB (D.cornerPoint d)))
    (C.affineProjectionTotal A joinedA (C.cornerPoint c))
  rw [S.affineProjectionSubdivision_parentPoint A joinedA B joinedB compatible]
  exact related

end Unfoldings.TriangleComplex.Subdivision
