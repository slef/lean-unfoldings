module

public import Unfoldings.Roof.ProjectedPointCopyValues
public import Unfoldings.Complex.VertexCopyFibers

/-! Closed physical contact identification determines the entire uncut intrinsic fiber. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- No contact between different physical points remains, including vertices and edges. -/
theorem forgetCuts_eq_of_closed_face_contact {retain : Set C.Seam}
    (D : FacewiseDevelopment C retain)
    (contacts : ∀ f g (p q : Plane),
      p ∈ (K.projectedTriangle f).carrier → q ∈ (K.projectedTriangle g).carrier →
      D.roofPlacement K f p = D.roofPlacement K g q → p = q)
    {x y : C.Realization retain} (same : D.toPlane x = D.toPlane y) :
    C.forgetCuts (Set.subset_univ _) x = C.forgetCuts (Set.subset_univ _) y := by
  obtain ⟨⟨f, a⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) x
  obtain ⟨⟨g, b⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) y
  have first : K.projectFace f a.val ∈ (K.projectedTriangle f).carrier := by
    rw [projectedTriangle, Triangle.affineImage_carrier]
    exact ⟨a.val, a.property, rfl⟩
  have last : K.projectFace g b.val ∈ (K.projectedTriangle g).carrier := by
    rw [projectedTriangle, Triangle.affineImage_carrier]
    exact ⟨b.val, b.property, rfl⟩
  have equal := contacts f g _ _ first last (by
    rw [D.roofPlacement_apply, D.roofPlacement_apply]
    exact same)
  apply K.projection_injective
  change Cap.horizontal (K.folding.toSpace Set.univ
      (C.forgetCuts (Set.subset_univ _) (C.faceMap retain f a))) =
    Cap.horizontal (K.folding.toSpace Set.univ
      (C.forgetCuts (Set.subset_univ _) (C.faceMap retain g b)))
  rw [C.forgetCuts_faceMap, C.forgetCuts_faceMap,
    K.folding.toSpace_faceMap, K.folding.toSpace_faceMap]
  exact equal

end Unfoldings.ConvexRoof
