module

public import Unfoldings.Complex.AffineProjectionSubdivisionVertices

/-! Corresponding actual points commute with a compatible change to projected face metrics. -/

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

theorem affineProjectionSubdivision_point {retain : Set C.Seam}
    {fineRetain : Set D.Seam} (H : S.Conforming retain fineRetain)
    (a : D.Total) (b : C.Total)
    (same : H.metricEquiv (MetricGluing.point D.Cell (D.glue fineRetain) a) =
      MetricGluing.point C.Cell (C.glue retain) b) :
    (S.affineProjectionSubdivision_conforming A joinedA B joinedB compatible H).metricEquiv
      (MetricGluing.point (D.affineProjectionComplex B joinedB).Cell
        ((D.affineProjectionComplex B joinedB).glue fineRetain)
        (D.affineProjectionTotal B joinedB a)) =
      MetricGluing.point (C.affineProjectionComplex A joinedA).Cell
        ((C.affineProjectionComplex A joinedA).glue retain)
        (C.affineProjectionTotal A joinedA b) := by
  let HP := S.affineProjectionSubdivision_conforming A joinedA B joinedB compatible H
  have old := (C.point_eq_iff retain _ _).mp same
  have related := C.affineProjection_eqvGen A joinedA retain old
  refine (HP.metricEquiv_faceMap a.1 (D.affineProjectionTotal B joinedB a).2).trans ?_
  apply ((C.affineProjectionComplex A joinedA).point_eq_iff retain _ _).mpr
  change Relation.EqvGen ((C.affineProjectionComplex A joinedA).glue retain)
    ((S.affineProjectionSubdivision A joinedA B joinedB compatible).parentPoint
      (D.affineProjectionTotal B joinedB a))
    (C.affineProjectionTotal A joinedA b)
  rw [S.affineProjectionSubdivision_parentPoint A joinedA B joinedB compatible]
  exact related

end Unfoldings.TriangleComplex.Subdivision
