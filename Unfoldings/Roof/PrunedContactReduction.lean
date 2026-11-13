module

public import Unfoldings.Roof.PrunedSeamContact
public import Unfoldings.Roof.ProjectedPointCopyValues

/-! All remaining self-contacts of the pruned development involve an actual intrinsic vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C M.retain}
  (B : M.SectorFrameData positive small D) (nonoverlap : D.Nonoverlapping)
  (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
  (physical_contacts : ∀ f g (p q : Plane),
    p ∈ (K.projectedTriangle f).carrier → q ∈ (K.projectedTriangle g).carrier →
    D.roofPlacement K f p = D.roofPlacement K g q →
      p = q ∨ (K.projectedTriangle f).IsVertex p ∨ (K.projectedTriangle g).IsVertex q)

include B budget physical_contacts in
/-- The finite-radius and pruning arguments remove every contact between intrinsic nonvertices. -/
theorem curved_contact_eq_or_vertex (x y : C.Realization M.curvedRetain)
    (same : (M.curvedDevelopment D nonoverlap).toPlane x =
      (M.curvedDevelopment D nonoverlap).toPlane y) :
    x = y ∨ x ∈ Set.range (C.vertexPoint M.curvedRetain) ∨
      y ∈ Set.range (C.vertexPoint M.curvedRetain) := by
  obtain ⟨⟨f, a⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue M.curvedRetain) x
  obtain ⟨⟨g, b⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue M.curvedRetain) y
  let p := K.projectFace f a.val
  let q := K.projectFace g b.val
  have first : p ∈ (K.projectedTriangle f).carrier := by
    rw [ConvexRoof.projectedTriangle, Triangle.affineImage_carrier]
    exact ⟨a.val, a.property, rfl⟩
  have last : q ∈ (K.projectedTriangle g).carrier := by
    rw [ConvexRoof.projectedTriangle, Triangle.affineImage_carrier]
    exact ⟨b.val, b.property, rfl⟩
  have first_copy : K.pointCopy M.curvedRetain f p first = C.faceMap M.curvedRetain f a :=
    K.pointCopy_of_localPoint M.curvedRetain f a
  have last_copy : K.pointCopy M.curvedRetain g q last = C.faceMap M.curvedRetain g b :=
    K.pointCopy_of_localPoint M.curvedRetain g b
  have actual : D.roofPlacement K f p = D.roofPlacement K g q := by
    rw [D.roofPlacement_apply, D.roofPlacement_apply]
    exact same
  change C.faceMap M.curvedRetain f a = C.faceMap M.curvedRetain g b ∨
    C.faceMap M.curvedRetain f a ∈ Set.range (C.vertexPoint M.curvedRetain) ∨
      C.faceMap M.curvedRetain g b ∈ Set.range (C.vertexPoint M.curvedRetain)
  rw [← first_copy, ← last_copy]
  rcases physical_contacts f g p q first last actual with physical | corner | corner
  · by_cases vertex : p ∈ Set.range K.projectedVertex
    · exact Or.inr (Or.inl
        (K.pointCopy_mem_vertices_of_physical_vertex M.curvedRetain f p first vertex))
    · have other : p ∈ (K.projectedTriangle g).carrier := physical.symm ▸ last
      have values : D.roofPlacement K f p = D.roofPlacement K g p := by
        rwa [← physical] at actual
      have equal := curved_pointCopy_eq_of_same_physical_point B f g first other vertex budget
        values
      exact Or.inl (by simpa only [physical] using equal)
  · exact Or.inr (Or.inl ((K.pointCopy_mem_vertices_iff M.curvedRetain f p first).mpr corner))
  · exact Or.inr (Or.inr ((K.pointCopy_mem_vertices_iff M.curvedRetain g q last).mpr corner))

include B budget physical_contacts in
/-- Global injectivity reduces to uniqueness of fibers through intrinsic vertices. -/
theorem curved_injective_iff_vertex_fibers_unique :
    Function.Injective (M.curvedDevelopment D nonoverlap).toPlane ↔
      ∀ v : C.Vertex M.curvedRetain, ∀ y : C.Realization M.curvedRetain,
        (M.curvedDevelopment D nonoverlap).toPlane (C.vertexPoint M.curvedRetain v) =
          (M.curvedDevelopment D nonoverlap).toPlane y → C.vertexPoint M.curvedRetain v = y := by
  refine ⟨fun injective v y same => injective same, ?_⟩
  intro unique x y same
  rcases curved_contact_eq_or_vertex B nonoverlap budget physical_contacts x y same with
    equal | ⟨v, at_first⟩ | ⟨v, at_last⟩
  · exact equal
  · rw [← at_first] at same ⊢
    exact unique v y same
  · rw [← at_last] at same ⊢
    exact (unique v x same.symm).symm

end Unfoldings.ConvexRoof.SectorForest
