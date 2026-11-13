module

public import Unfoldings.Roof.GeometricSectorData

/-! Every active geometric component has an actual seed-to-tip edge in the cut forest. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outer : Set Plane} (F : K.SkirtTailFamily outer (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1)

theorem geometric_component_nonconstant (w : F.GeometricVertex)
    (nonroot : w ∉ (M.geometricParents F covered positive small).roots) :
    F.componentSeed (M.geometricComponent F covered w) ≠
      (F.componentTail (M.geometricComponent F covered w)).tip := by
  cases w with
  | inl w =>
    let c := M.geometricComponent F covered (Sum.inl w)
    have seed : K.projectedVertex (M.parents.root w) = F.componentSeed c :=
      F.rim_vertex_eq_seed c (M.parents.root w) (M.rootPath_end_boundary w)
        (F.rimComponent_mem covered (M.parents.root w) (M.rootPath_end_boundary w))
    intro equal
    exact F.rim_vertex_ne_tip c (M.parents.root w) (seed.trans equal)
  | inr w =>
    cases w with
    | inl c => exact c.property.1
    | inr c => exact (nonroot ⟨c, rfl⟩).elim

theorem exists_geometric_component_radial_edge (c : F.Component)
    (genuine : F.componentSeed c ≠ (F.componentTail c).tip) :
    ∃ w : F.GeometricVertex,
      w ∉ (M.geometricParents F covered positive small).roots ∧
        M.geometricComponent F covered w = c ∧ F.geometricPosition w = F.componentSeed c ∧
          M.geometricParent F covered w = Sum.inr (Sum.inr c) := by
  classical
  by_cases attached : ∃ w : C.Vertex Set.univ,
      C.IsBoundaryVertex Set.univ w ∧ K.projectedVertex w = F.componentSeed c
  · obtain ⟨w, boundary, seed⟩ := attached
    have component : F.rimComponent covered w boundary = c :=
      F.rimComponent_eq_of_member covered w boundary c
        (seed.symm ▸ (F.componentTail c).seed_mem)
    refine ⟨Sum.inl w, M.geometric_original_nonroot F covered positive small w,
      (M.geometricComponent_rim F covered w boundary).trans component, seed, ?_⟩
    simp only [geometricParent, dite_eq_left boundary, component]
  · let d : F.IndependentComponent := ⟨c, genuine, attached⟩
    exact ⟨Sum.inr (Sum.inl d),
      M.geometric_independent_nonroot F covered positive small d, rfl, rfl, rfl⟩

end Unfoldings.ConvexRoof.SectorForest
