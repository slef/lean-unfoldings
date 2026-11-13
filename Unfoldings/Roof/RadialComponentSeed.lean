module

public import Unfoldings.Roof.SectorBoundaryComponents
public import Unfoldings.Roof.GeometricRadialEdges

/-! Every nonroot geometric node of a pure radial component is its single seed. -/

@[expose] public section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outerDomain : Set Plane} (F : K.SkirtTailFamily outerDomain (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1) (c : F.Component)
  (unattached : ∀ e : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
    M.cutPieceLabel F covered (Sum.inl e) ≠ c)

include unattached

theorem unattached_component_nonroot_position_eq_seed (w : F.GeometricVertex)
    (nonroot : w ∉ (M.geometricParents F covered positive small).roots)
    (component : M.geometricComponent F covered w = c) :
    F.geometricPosition w = F.componentSeed c := by
  cases w with
  | inl w =>
    by_cases boundary : C.IsBoundaryVertex Set.univ w
    · exact F.rim_vertex_eq_seed c w boundary
        (M.unattached_component_positions_on_tail F covered c unattached (Sum.inl w) component)
    · have old_nonroot : w ∉ M.parents.roots := by
        simpa only [M.roots_eq, Set.mem_ofPred_eq] using boundary
      exact (unattached ⟨w, old_nonroot⟩ component).elim
  | inr w =>
    cases w with
    | inl d =>
      change d.val = c at component
      exact congrArg F.componentSeed component
    | inr d => exact (nonroot ⟨d, rfl⟩).elim

theorem fine_coherent_seed_of_unattached_leaf {i : FiveSector}
    (leaf : M.GeometricSectorLeaf F covered positive small i)
    (component : M.geometricComponent F covered leaf.val = c)
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    (Q : ConvexCap FineC) {retain : Set FineC.Seam} (D : FacewiseDevelopment FineC retain)
    (represented : ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (coherent : D.ProjectedCoherentAt Q (F.geometricPosition leaf.val)) :
    ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.componentSeed c ∧
      D.ProjectedCoherentAt Q (Q.projectedVertex w) ∧
      Q.projectedVertex w ∈ (F.componentTail c).carrier := by
  obtain ⟨w, at_leaf⟩ := represented
  have seed := M.unattached_component_nonroot_position_eq_seed F covered positive small c
    unattached leaf.val leaf.property.1 component
  refine ⟨w, at_leaf.trans seed, at_leaf.symm ▸ coherent, ?_⟩
  rw [at_leaf, seed]
  exact (F.componentTail c).seed_mem

end Unfoldings.ConvexRoof.SectorForest
