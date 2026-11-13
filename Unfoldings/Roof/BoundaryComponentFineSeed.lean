module

public import Unfoldings.Roof.RadialComponentSeed
public import Unfoldings.Roof.GeometricWaterfallAvoidance

/-! Any radial component meeting a sector bank inside the clip has a coherent fine seed. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outerDomain : Set Plane} (F : K.SkirtTailFamily outerDomain (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1)

theorem fine_coherent_seed_of_boundary_component
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    (Q : ConvexCap FineC) {retain : Set FineC.Seam} (D : FacewiseDevelopment FineC retain)
    (represented : ∀ i, ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (coherent : ∀ i, ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    (c : F.Component) {x : Plane} (member : x ∈ (F.componentTail c).carrier)
    (inside : x ∈ interior (outerDomain))
    (boundary : ∀ i, x - origin ∉ strictFiveSector t i) :
    (∀ e : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
      M.cutPieceLabel F covered (Sum.inl e) ≠ c) ∧
    ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.componentSeed c ∧
      D.ProjectedCoherentAt Q (Q.projectedVertex w) ∧
      Q.projectedVertex w ∈ (F.componentTail c).carrier := by
  have unattached := M.sector_boundary_component_unattached positive small F covered member boundary
  have genuine : F.componentSeed c ≠ (F.componentTail c).tip := by
    intro equal
    have at_tip : x = (F.componentTail c).tip := by
      have on_segment : x ∈ segment ℝ (F.componentSeed c) (F.componentTail c).tip := member
      simpa only [equal, segment_same, Set.mem_singleton_iff] using on_segment
    exact (F.componentTail c).boundary.2 (at_tip ▸ inside)
  obtain ⟨a, nonroot, component, _, _⟩ :=
    M.exists_geometric_component_radial_edge F covered positive small c genuine
  let i := (M.geometricComponentSector F covered positive small c).sector
  obtain ⟨leaf, ancestor, _⟩ :=
    M.exists_geometric_sector_leaf_support F covered positive small
    i a nonroot (by rw [component]) (left_mem_segment ℝ _ _)
  have leaf_component : M.geometricComponent F covered leaf.val = c :=
    (M.geometricComponent_of_ancestor F covered positive small ancestor).trans component
  exact ⟨unattached, M.fine_coherent_seed_of_unattached_leaf F covered positive small c
    unattached leaf leaf_component Q D (represented i leaf) (coherent i leaf)⟩

end Unfoldings.ConvexRoof.SectorForest
