module

public import Unfoldings.Cap.GeometricFreshWaterfallLeaf

public import Unfoldings.Roof.GeometricTailLeaves
public import Unfoldings.Roof.GeometricTailCutoff
public import Unfoldings.Geometry.FiniteWaterfall
public import Unfoldings.Geometry.RayStripWidth
public import Unfoldings.Geometry.WedgeFrameSides
public import Unfoldings.Geometry.SubdivisionFreshTargets

/-! A fresh actual leaf is inserted in a positive-width cell, unless it is the source itself. -/

@[expose] public section

noncomputable section

namespace Unfoldings

namespace ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outer : Set Plane} (F : K.SkirtTailFamily outer (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1)

/-- Only earlier, distinct actual leaves are represented by existing separators.
A new leaf is not on any of their tails, including at tied insertion heights. -/
theorem geometric_leaf_positive_cell_width {i : FiveSector} {cutoff : ℝ}
    (deep : Metric.closedBall (origin) cutoff ⊆ interior outer)
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (leaf : M.GeometricSectorLeaf F covered positive small i)
    (active : leaf.point.re + leaf.point.im ≤ cutoff)
    (provenance : ∀ G ∈ P.separators,
      ∃ older : M.GeometricSectorLeaf F covered positive small i,
        older.val ≠ leaf.val ∧ older.point.re + older.point.im ≤ leaf.point.re + leaf.point.im ∧
        MonotoneStrip.CompletesTail older.point older.tailGraph.graph cutoff G)
    {S : MonotoneStrip} (cell : S ∈ P.cells) (member : leaf.point ∈ S.carrier) :
    leaf.point.re + leaf.point.im = 0 ∨
      S.lower.coordinate (leaf.point.re + leaf.point.im) <
        S.upper.coordinate (leaf.point.re + leaf.point.im) := by
  by_cases zero : leaf.point.re + leaf.point.im = 0
  · exact Or.inl zero
  have after_source : 0 < leaf.point.re + leaf.point.im :=
    lt_of_le_of_ne (add_nonneg leaf.point_nonnegative.1 leaf.point_nonnegative.2) (Ne.symm zero)
  apply Or.inr
  apply P.cell_positive_width_of_avoids_separators cell member
    ((fiveSectorFrame t positive small i).enclosingStrip_width_pos
      (fiveSector_banks_orient_pos positive small i) after_source)
  intro G wall same
  obtain ⟨older, different, before, completion⟩ := provenance G wall
  have avoids := older.tailGraph.leaf_coordinate_ne leaf.property.1 leaf.property.2.1 different
    before (active.trans_lt (older.tail_end_beyond_clip_ball deep))
  rw [completion.2 _ ⟨before, active⟩] at same
  exact avoids same

end ConvexRoof.SectorForest
end Unfoldings
