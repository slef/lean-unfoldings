module

public import Unfoldings.Roof.RestrictedEmbedding
public import Unfoldings.Roof.SelectionComponentDisk

/-! Convex-gradient selection components are intrinsic disks with injective planar projection. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
/-- The actual projection of a whole-face restriction covers precisely its closed face union. -/
theorem range_restrictProjection (U : Set Face) :
    Set.range (K.restrictProjection U) = K.restrictedCarrier U := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨⟨f, y⟩, rfl⟩ := MetricGluing.point_surjective
      (C.restrictFaces U).Cell ((C.restrictFaces U).glue Set.univ) x
    exact Set.mem_iUnion.mpr ⟨f, by
      rw [projectedTriangle, Triangle.affineImage_carrier]
      exact ⟨y.val, y.property, rfl⟩⟩
  · intro member
    obtain ⟨f, inside⟩ := Set.mem_iUnion.mp member
    rw [projectedTriangle, Triangle.affineImage_carrier] at inside
    obtain ⟨y, hy, image⟩ := inside
    exact ⟨(C.restrictFaces U).faceMap Set.univ f ⟨y, hy⟩, image⟩

open Classical in
/-- A Jordan whole-face roof restriction is homeomorphic to its entire actual planar image. -/
def restrictProjectionHomeomorph (U : Set Face) (nonempty : U.Nonempty)
    (jordan : Schoenflies.IsJordanCurve (frontier (K.restrictedCarrier U))) :
    (C.restrictFaces U).Realization Set.univ ≃ₜ K.restrictedCarrier U := by
  let f : (C.restrictFaces U).Realization Set.univ → K.restrictedCarrier U :=
    fun x => ⟨K.restrictProjection U x, (K.range_restrictProjection U).subset ⟨x, rfl⟩⟩
  have continuous : Continuous f := (K.restrictProjection U).continuous.subtype_mk _
  have injective : Function.Injective f := fun _ _ same =>
    K.restrictProjection_injective_of_Jordan U nonempty jordan (congrArg Subtype.val same)
  have surjective : Function.Surjective f := by
    intro p
    obtain ⟨x, image⟩ := (K.range_restrictProjection U).symm.subset p.property
    exact ⟨x, Subtype.ext image⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f ⟨injective, surjective⟩) continuous

open Classical in
/-- Convex-gradient component disks have no collapsed intrinsic vertex copies. -/
theorem selectionComponent_projection_injective {slopes : Set Plane}
    (convex : Convex ℝ slopes) (closed : IsClosed slopes) (seed : Face)
    (selected : K.normalSlope seed ∈ slopes) :
    Function.Injective (K.restrictProjection (K.selectionComponent slopes seed)) :=
  K.restrictProjection_injective_of_Jordan _ ⟨seed, K.seed_mem_selectionComponent slopes seed⟩
    (K.selectionComponent_frontier_isJordan convex closed seed selected)

open Classical in
/-- Every nonempty whole-edge component of a convex-gradient selection is an intrinsic closed
cut disk. Its metric comes from the original whole faces and inherited original seams. -/
theorem exists_selectionComponent_intrinsic_disk {slopes : Set Plane}
    (convex : Convex ℝ slopes) (closed : IsClosed slopes) (seed : Face)
    (selected : K.normalSlope seed ∈ slopes) :
    Nonempty ((C.restrictFaces (K.selectionComponent slopes seed)).Realization Set.univ ≃ₜ
      Metric.closedBall (0 : Plane) 1) := by
  obtain ⟨disk⟩ := K.exists_selectionComponent_disk convex closed seed selected
  exact ⟨(K.restrictProjectionHomeomorph _ ⟨seed, K.seed_mem_selectionComponent slopes seed⟩
    (K.selectionComponent_frontier_isJordan convex closed seed selected)).trans disk⟩

open Classical in
/-- A closed convex gradient selection has intrinsic disk components with injective projection
and simple Jordan frontier, including at boundary vertices and contacts with other components. -/
theorem convex_gradient_selection_component {slopes : Set Plane}
    (convex : Convex ℝ slopes) (closed : IsClosed slopes) (seed : Face)
    (selected : K.normalSlope seed ∈ slopes) :
    Function.Injective (K.restrictProjection (K.selectionComponent slopes seed)) ∧
    Nonempty ((C.restrictFaces (K.selectionComponent slopes seed)).Realization Set.univ ≃ₜ
      Metric.closedBall (0 : Plane) 1) ∧
    Schoenflies.IsJordanCurve
      (frontier (K.restrictedCarrier (K.selectionComponent slopes seed))) :=
  ⟨K.selectionComponent_projection_injective convex closed seed selected,
    K.exists_selectionComponent_intrinsic_disk convex closed seed selected,
    K.selectionComponent_frontier_isJordan convex closed seed selected⟩

end Unfoldings.ConvexRoof
