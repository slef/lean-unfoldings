module

public import Unfoldings.Cap.SectorBoundaryCutPoints
public import Unfoldings.Roof.GeometricSectorBankPoints
public import Unfoldings.Cap.ExtendedWaterfallDomains
public import Unfoldings.Cap.ProjectedCoherence

/-! Cuts on sector boundary rays are radial skirt pieces or actual leaf endpoints. -/

@[expose] public section

noncomputable section

namespace Unfoldings

namespace ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  (positive : 0 < t) (small : t < 1)

include positive small

/-- Every positive portion of an original outgoing edge lies strictly inside
its assigned sector. Only its starting vertex can lie on a boundary ray. -/
theorem original_parent_point_strict_or_start
    (e : {w : C.Vertex Set.univ // w ∉ M.parents.roots}) {x : Plane}
    (member : x ∈ segment ℝ (K.projectedVertex e.val)
      (K.projectedVertex (M.parents.parent e.val))) :
    x = K.projectedVertex e.val ∨
      x - origin ∈
        strictFiveSector t (Sum.inl (K.sourceSectorLabel t origin e.val)) := by
  obtain ⟨r, bounds, expression⟩ := (segment_eq_image_lineMap ℝ
    (K.projectedVertex e.val) (K.projectedVertex (M.parents.parent e.val))).subset member
  by_cases zero : r = 0
  · left
    rw [zero, AffineMap.lineMap_apply_zero] at expression
    exact expression.symm
  · right
    have rpositive : 0 < r := lt_of_le_of_ne bounds.1 (Ne.symm zero)
    have internal : ¬ C.IsBoundaryVertex Set.univ e.val := by
      simpa only [M.roots_eq, Set.mem_ofPred_eq] using e.property
    have position := mem_closedThreeSector_label_of_backward positive.le small
      (p := K.projectedVertex e.val - origin)
      (sub_nonpos.mpr (M.maximal e.val internal))
    have direction := M.direction e.val e.property
    have vector : x - origin =
        (K.projectedVertex e.val - origin) +
          r • (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val) := by
      rw [← expression, AffineMap.lineMap_apply_module']
      abel
    change 0 < threeSectorCoordinates t (K.sourceSectorLabel t origin e.val)
        (x - origin) 0 ∧
      0 < threeSectorCoordinates t (K.sourceSectorLabel t origin e.val)
        (x - origin) 1
    rw [vector, map_add, map_smul]
    exact ⟨add_pos_of_nonneg_of_pos position.1 (mul_pos rpositive direction.1),
      add_pos_of_nonneg_of_pos position.2 (mul_pos rpositive direction.2)⟩

variable {outerDomain : Set Plane} (F : K.SkirtTailFamily outerDomain (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)


/-- This is a geometric classification of actual cuts, including contacts
at vertices. It does not assume that a boundary ray is uncut. -/
theorem sector_boundary_cut_point_on_skirt_or_leaf {x : Plane}
    (boundary : ∀ i, x - origin ∉ strictFiveSector t i)
    (on_cut : x ∈ M.extendedGeometricCuts F) :
    (∃ c : F.Component, x ∈ (F.componentTail c).carrier) ∨
      ∃ i, ∃ leaf : M.GeometricSectorLeaf F covered positive small i,
        F.geometricPosition leaf.val = x := by
  rw [M.extendedGeometricCuts_eq_piece_union F] at on_cut
  obtain ⟨e | c, member⟩ := Set.mem_iUnion.mp on_cut
  · rcases M.original_parent_point_strict_or_start positive small e member with at_start | strict
    · right
      have nonroot := M.geometric_original_nonroot F covered positive small e.val
      have childless := M.geometric_sector_bank_childless F covered positive small
        (Sum.inl e.val) nonroot (by
          change K.projectedVertex e.val - origin ∉ _
          rw [← at_start]
          exact boundary _)
      refine ⟨_, ⟨Sum.inl e.val, nonroot, childless, rfl⟩, ?_⟩
      exact at_start.symm
    · exact (boundary _ strict).elim
  · exact Or.inl ⟨c, member⟩

universe u₁ v₁

/-- The only possible two-bank boundary contact is on a genuine radial
skirt component. Every other boundary point has one actual developed value. -/
theorem sector_boundary_coherent_or_skirt
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain)
    (leaf_coherent : ∀ i, ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    {x : Plane} (boundary : ∀ i, x - origin ∉ strictFiveSector t i) :
    D.ProjectedCoherentAt Q x ∨ ∃ c : F.Component, x ∈ (F.componentTail c).carrier := by
  by_cases on_cut : x ∈ M.extendedGeometricCuts F
  · rcases M.sector_boundary_cut_point_on_skirt_or_leaf positive small F covered
      boundary on_cut with skirt | ⟨i, leaf, at_leaf⟩
    · exact Or.inr skirt
    · left
      rw [← at_leaf]
      exact leaf_coherent i leaf
  · exact Or.inl (D.projected_coherentAt_of_not_cut Q
      (fun member => on_cut (R.projectedCutSet_subset member)))

end ConvexRoof.SectorForest
end Unfoldings
