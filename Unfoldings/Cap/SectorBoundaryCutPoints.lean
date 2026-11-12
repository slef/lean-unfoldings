module

public import Unfoldings.Cap.GeometricSectorBankPoints
public import Unfoldings.Cap.ExtendedWaterfallDomains
public import Unfoldings.Cap.ProjectedCoherence

/-! Cuts on sector boundary rays are radial skirt pieces or actual leaf endpoints. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem not_strictFiveSector_of_boundary {t : ℝ} (positive : 0 < t) (small : t < 1)
    {i : FiveSector} {x : Plane} (inside : x ∈ closedFiveSector t i)
    (boundary : x ∉ strictFiveSector t i) : ∀ j, x ∉ strictFiveSector t j := by
  intro j strict
  by_cases same : j = i
  · exact boundary (same ▸ strict)
  · exact Set.disjoint_left.mp (strictFiveSector_disjoint_closed positive small same) strict inside

theorem fiveSector_enclosingStrip_bank_closed {t : ℝ} (positive : 0 < t) (small : t < 1)
    (i : FiveSector) {h : ℝ} (nonnegative : 0 ≤ h) :
    let B := fiveSectorFrame t positive small i
    B.place.symm (B.enclosingStrip.lower.point h) ∈ closedFiveSector t i ∧
      B.place.symm (B.enclosingStrip.upper.point h) ∈ closedFiveSector t i := by
  let B := fiveSectorFrame t positive small i
  have first_quad := B.quadrant_self
    (x := fiveSectorFirst t i) ⟨1, 0, by norm_num, le_rfl, by simp⟩ B.first_ne
  have last_quad := B.quadrant_self
    (x := fiveSectorLast t i) ⟨0, 1, le_rfl, by norm_num, by simp⟩ B.last_ne
  let P := MonotoneHeightGraph.ray (B.place (fiveSectorFirst t i)) first_quad.1 first_quad.2
  let Q := MonotoneHeightGraph.ray (B.place (fiveSectorLast t i)) last_quad.1 last_quad.2
  have ray_inside (v : Plane) (inside : v ∈ closedFiveSector t i)
      (quad : 0 < (B.place v).re ∧ 0 < (B.place v).im) :
      B.place.symm ((MonotoneHeightGraph.ray (B.place v) quad.1 quad.2).point h) ∈
        closedFiveSector t i := by
    rw [MonotoneHeightGraph.ray_point_eq_smul, map_smul, map_smul, B.place.symm_apply_apply]
    exact (inside.nonneg_smul (inv_nonneg.mpr (add_pos quad.1 quad.2).le)).nonneg_smul nonnegative
  have first : B.place.symm (P.point h) ∈ closedFiveSector t i :=
    ray_inside _ ⟨1, 0, by norm_num, le_rfl, by simp⟩ first_quad
  have last : B.place.symm (Q.point h) ∈ closedFiveSector t i :=
    ray_inside _ ⟨0, 1, le_rfl, by norm_num, by simp⟩ last_quad
  constructor
  · change B.place.symm ((P.min Q).point h) ∈ closedFiveSector t i
    rcases P.min_point_eq_or Q h with equal | equal
    · exact equal.symm ▸ first
    · exact equal.symm ▸ last
  · change B.place.symm ((P.max Q).point h) ∈ closedFiveSector t i
    rcases P.max_point_eq_or Q h with equal | equal
    · exact equal.symm ▸ first
    · exact equal.symm ▸ last

theorem fiveSector_enclosingStrip_bank_not_strict_any
    {t : ℝ} (positive : 0 < t) (small : t < 1) (i : FiveSector)
    {h : ℝ} (nonnegative : 0 ≤ h) :
    let B := fiveSectorFrame t positive small i
    (∀ j, B.place.symm (B.enclosingStrip.lower.point h) ∉ strictFiveSector t j) ∧
      (∀ j, B.place.symm (B.enclosingStrip.upper.point h) ∉ strictFiveSector t j) := by
  have closed := fiveSector_enclosingStrip_bank_closed positive small i nonnegative
  have boundary := fiveSector_enclosingStrip_bank_not_strict positive small i h
  exact ⟨not_strictFiveSector_of_boundary positive small closed.1 boundary.1,
    not_strictFiveSector_of_boundary positive small closed.2 boundary.2⟩

namespace ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  (positive : 0 < t) (small : t < 1)

include positive small

/-- Every positive portion of an original outgoing edge lies strictly inside
its assigned sector. Only its starting vertex can lie on a boundary ray. -/
theorem original_parent_point_strict_or_start
    (e : {w : C.Vertex Set.univ // w ∉ M.parents.roots}) {x : Plane}
    (member : x ∈ segment ℝ (K.projectedVertex e.val)
      (K.projectedVertex (M.parents.parent e.val))) :
    x = K.projectedVertex e.val ∨
      x - K.projectedVertex origin ∈
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
      (p := K.projectedVertex e.val - K.projectedVertex origin)
      (sub_nonpos.mpr (M.maximal e.val internal))
    have direction := M.direction e.val e.property
    have vector : x - K.projectedVertex origin =
        (K.projectedVertex e.val - K.projectedVertex origin) +
          r • (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val) := by
      rw [← expression, AffineMap.lineMap_apply_module']
      abel
    change 0 < threeSectorCoordinates t (K.sourceSectorLabel t origin e.val)
        (x - K.projectedVertex origin) 0 ∧
      0 < threeSectorCoordinates t (K.sourceSectorLabel t origin e.val)
        (x - K.projectedVertex origin) 1
    rw [vector, map_add, map_smul]
    exact ⟨add_pos_of_nonneg_of_pos position.1 (mul_pos rpositive direction.1),
      add_pos_of_nonneg_of_pos position.2 (mul_pos rpositive direction.2)⟩

variable {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (lower : Z < 0)

/-- This is a geometric classification of actual cuts, including contacts
at vertices. It does not assume that a boundary ray is uncut. -/
theorem sector_boundary_cut_point_on_skirt_or_leaf {x : Plane}
    (boundary : ∀ i, x - K.projectedVertex origin ∉ strictFiveSector t i)
    (on_cut : x ∈ M.extendedGeometricCuts F) :
    (∃ c : F.Component, x ∈ (F.componentTail c).carrier) ∨
      ∃ i, ∃ leaf : M.GeometricSectorLeaf F covered positive small lower i,
        F.geometricPosition leaf.val = x := by
  rw [M.extendedGeometricCuts_eq_piece_union F] at on_cut
  obtain ⟨e | c, member⟩ := Set.mem_iUnion.mp on_cut
  · rcases M.original_parent_point_strict_or_start positive small e member with at_start | strict
    · right
      have nonroot := M.geometric_original_nonroot F covered positive small lower e.val
      have childless := M.geometric_sector_bank_childless F covered positive small lower
        (Sum.inl e.val) nonroot (by
          change K.projectedVertex e.val - K.projectedVertex origin ∉ _
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
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain)
    (leaf_coherent : ∀ i, ∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    {x : Plane} (boundary : ∀ i, x - K.projectedVertex origin ∉ strictFiveSector t i) :
    D.ProjectedCoherentAt Q x ∨ ∃ c : F.Component, x ∈ (F.componentTail c).carrier := by
  by_cases on_cut : x ∈ M.extendedGeometricCuts F
  · rcases M.sector_boundary_cut_point_on_skirt_or_leaf positive small F covered lower
      boundary on_cut with skirt | ⟨i, leaf, at_leaf⟩
    · exact Or.inr skirt
    · left
      rw [← at_leaf]
      exact leaf_coherent i leaf
  · exact Or.inl (D.projected_coherentAt_of_not_cut Q
      (fun member => on_cut (R.projectedCutSet_subset member)))

end ConvexCap.SectorForest
end Unfoldings
