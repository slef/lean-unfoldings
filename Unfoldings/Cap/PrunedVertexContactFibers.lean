module

public import Unfoldings.Cap.PrunedContactReduction
public import Unfoldings.Cap.ClosedContactFibers

/-! All remaining pruned contacts are between intrinsic copies of one physical vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C M.retain}
  (B : M.SectorFrameData positive small D) (nonoverlap : D.Nonoverlapping)
  (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
  (physical_contacts : ∀ f g (p q : Plane),
    p ∈ (K.projectedTriangle f).carrier → q ∈ (K.projectedTriangle g).carrier →
    D.projectedPlacement K f p = D.projectedPlacement K g q → p = q)

include B budget physical_contacts

/-- No remaining vertex-edge contact or contact between different physical vertices is possible. -/
theorem curved_contact_eq_or_same_original_vertices (x y : C.Realization M.curvedRetain)
    (same : (M.curvedDevelopment D nonoverlap).toPlane x =
      (M.curvedDevelopment D nonoverlap).toPlane y) :
    x = y ∨ ∃ v w : C.Vertex M.curvedRetain,
      C.vertexPoint M.curvedRetain v = x ∧ C.vertexPoint M.curvedRetain w = y ∧
        C.vertexForgetCuts (Set.subset_univ _) v =
          C.vertexForgetCuts (Set.subset_univ _) w := by
  have physical : ∀ f g (p q : Plane),
      p ∈ (K.projectedTriangle f).carrier → q ∈ (K.projectedTriangle g).carrier →
      (M.curvedDevelopment D nonoverlap).projectedPlacement K f p =
        (M.curvedDevelopment D nonoverlap).projectedPlacement K g q → p = q :=
    physical_contacts
  have original := K.forgetCuts_eq_of_closed_face_contact
    (M.curvedDevelopment D nonoverlap) physical same
  rcases curved_contact_eq_or_vertex B nonoverlap budget
    (fun f g p q first last same => Or.inl (physical_contacts f g p q first last same))
    x y same with equal | ⟨v, first⟩ | ⟨w, last⟩
  · exact Or.inl equal
  · obtain ⟨w, last, labels⟩ := C.exists_vertex_copy_of_forgetCuts_eq
      (Set.subset_univ _) v y (by rwa [first])
    exact Or.inr ⟨v, w, first, last, labels⟩
  · obtain ⟨v, first, labels⟩ := C.exists_vertex_copy_of_forgetCuts_eq
      (Set.subset_univ _) w x (by rw [last]; exact original.symm)
    exact Or.inr ⟨v, w, first, last, labels.symm⟩

/-- Global injectivity now asks only whether equal-image copies of one original vertex
are identified by the retained link pairings. -/
theorem curved_injective_iff_same_original_vertex_copies_unique :
    Function.Injective (M.curvedDevelopment D nonoverlap).toPlane ↔
      ∀ v w : C.Vertex M.curvedRetain,
        C.vertexForgetCuts (Set.subset_univ _) v =
          C.vertexForgetCuts (Set.subset_univ _) w →
        (M.curvedDevelopment D nonoverlap).toPlane (C.vertexPoint M.curvedRetain v) =
          (M.curvedDevelopment D nonoverlap).toPlane (C.vertexPoint M.curvedRetain w) → v = w := by
  refine ⟨fun injective v w _ same => C.vertexPoint_injective _ (injective same), ?_⟩
  intro unique x y same
  rcases curved_contact_eq_or_same_original_vertices B nonoverlap budget physical_contacts
    x y same with equal | ⟨v, w, first, last, labels⟩
  · exact equal
  · rw [← first, ← last] at same ⊢
    exact congrArg (C.vertexPoint M.curvedRetain) (unique v w labels same)

end Unfoldings.ConvexCap.SectorForest
