module

public import Unfoldings.Cap.GeometricWaterfall
public import Unfoldings.Cap.GeometricBankPersistence
public import Unfoldings.Cap.StrictGeometricTailGraphs
public import Unfoldings.Geometry.RecoverableWaterfall
public import Unfoldings.Cap.GeometricTailAffine
public import Unfoldings.Geometry.VertexPinchWaterfall
public import Unfoldings.Cap.GeometricFreshWaterfallLeaf
public import Unfoldings.Geometry.StripInsertionTerminalTail

/-! Every constructed actual sector waterfall reopens only at its source or geometric leaves. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1) (lower : Z < 0)

/-- Actual geometry supplies every persistence and strictness hypothesis of the finite
construction. No pinch classification, strip cover, or compatible map is an input. -/
theorem exists_geometric_sector_waterfall_with_terminal_tails (i : FiveSector) (cutoff : ℝ)
    (tips_beyond : ∀ w : M.GeometricSectorLeaf F covered positive small lower i,
      w.point.re + w.point.im ≤ cutoff →
        cutoff < M.geometricTailEndHeight F covered positive small lower i w.val) :
    let E := insert (0 : ℂ) (Set.range (fun w :
      M.GeometricSectorLeaf F covered positive small lower i => w.point))
    let V := Set.range (fun w : F.GeometricVertex =>
      (fiveSectorFrame t positive small i).place (F.geometricPosition w - K.projectedVertex origin))
    ∃ T : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
      (∀ G ∈ T.separators,
        ∃ w : M.GeometricSectorLeaf F covered positive small lower i,
          w.point.re + w.point.im ≤ cutoff ∧
            MonotoneStrip.CompletesTail w.point w.tailGraph.graph cutoff G) ∧
      (∀ w : M.GeometricSectorLeaf F covered positive small lower i,
        w.point.re + w.point.im ≤ cutoff →
          ∃ G ∈ T.separators,
            MonotoneStrip.CompletesTail w.point w.tailGraph.graph cutoff G) ∧
      ∀ R ∈ T.cells, (R.lower.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧
        R.upper.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧ R.RecoverablePinchesIn E 0 cutoff) ∧
          R.ApproachedPinchesIn V 0 cutoff ∧ R.TerminalTailsFrom
            (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
            (fun leaf => leaf.tailGraph.graph) cutoff := by
  let Leaf := M.GeometricSectorLeaf F covered positive small lower i
  let E := insert (0 : ℂ) (Set.range (fun w : Leaf => w.point))
  let Active := {w : Leaf // w.point.re + w.point.im ≤ cutoff}
  obtain ⟨n, e, ordered⟩ := exists_height_ordered_equiv
    (fun w : Active => w.val.point.re + w.val.point.im)
  let p : Fin n → ℂ := fun j => (e j).val.point
  let tail : Fin n → MonotoneHeightGraph := fun j => (e j).val.tailGraph.graph
  let B := fiveSectorFrame t positive small i
  let S := B.enclosingStrip
  let V := Set.range (fun w : F.GeometricVertex =>
    B.place (F.geometricPosition w - K.projectedVertex origin))
  have sources := B.enclosingStrip_source
  have initial : S.lower.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧
      S.upper.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧ S.RecoverablePinchesIn E 0 cutoff := by
    refine ⟨(B.enclosingStrip_strictCoordinatesOn _).1,
      (B.enclosingStrip_strictCoordinatesOn _).2, ?_⟩
    intro h slab same k later width
    exact Or.inl (B.enclosingStrip_recoverablePinchesIn cutoff h slab same k later width)
  have vertex_pinches : S.ApproachedPinchesIn V 0 cutoff := by
    intro h bounds same closed
    have affine := B.enclosingStrip_affineAt bounds.1
    exact (S.not_mem_closure_strictCarrier_of_affine_pinch affine.1 affine.2 same closed).elim
  have terminal_initial : S.TerminalTailsFrom (fun leaf : Leaf => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff := by
    intro h bounds merged
    exact ((B.enclosingStrip_width_pos (fiveSector_banks_orient_pos positive small i)
      bounds.1).ne (merged h ⟨le_rfl, bounds.2.le⟩)).elim
  obtain ⟨T, provenance, represented, good⟩ :=
    S.exists_finite_waterfall_vertex_pinches_preserving n p tail
    cutoff sources.1 sources.2 (fun j => (e j).val.point_nonnegative) ordered
    (fun j => (e j).property) (fun j => (e j).val.tailGraph_target)
    (fun j h inside => by
      have member := (e j).val.tailGraph_mem_strip inside.1
        (inside.2.trans_lt (tips_beyond (e j).val (e j).property))
      change S.lower.coordinate (((tail j).point h).re + ((tail j).point h).im) ≤
        (tail j).coordinate h ∧ (tail j).coordinate h ≤
          S.upper.coordinate (((tail j).point h).re + ((tail j).point h).im) at member
      rwa [(tail j).point_height] at member)
    (fun j k before => (e j).val.tailGraph.coalesces (e k).val.tailGraph
      (ordered before.le) le_rfl (tips_beyond (e j).val (e j).property)
      (tips_beyond (e k).val (e k).property)) E initial (fun j => Or.inr ⟨(e j).val, rfl⟩)
    (fun j => (e j).val.tailGraph.strictCoordinatesOn le_rfl
      (tips_beyond (e j).val (e j).property))
    (fun j h slab same k later =>
      (e j).val.tailGraph_enclosing_wall_sticks S.lower (Or.inl rfl) slab.1 slab.2
        (tips_beyond (e j).val (e j).property) same k later)
    (fun j h slab same k later =>
      ((e j).val.tailGraph_enclosing_wall_sticks S.upper (Or.inr rfl) slab.1 slab.2
        (tips_beyond (e j).val (e j).property) same.symm k later).symm)
    V vertex_pinches (fun j => ⟨(e j).val.val, rfl⟩)
    (fun h bounds _ => (B.enclosingStrip_affineAt bounds.1).1)
    (fun h bounds _ => (B.enclosingStrip_affineAt bounds.1).2)
    (fun j h within outside => (e j).val.tailGraph.affineAt_of_ne_vertices within.1
      (within.2.trans (tips_beyond (e j).val (e j).property))
      (fun w equal => outside ⟨w, equal.symm⟩))
    (fun R => R.TerminalTailsFrom (fun leaf : Leaf => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff) terminal_initial
    (fun j R member left_wall right_wall trapped first_strict last_strict _ => by
      have target_width : (p j).re + (p j).im = 0 ∨
          R.lower.coordinate ((p j).re + (p j).im) <
            R.upper.coordinate ((p j).re + (p j).im) := by
        by_cases zero : (p j).re + (p j).im = 0
        · exact Or.inl zero
        apply Or.inr
        have after_source : 0 < (p j).re + (p j).im :=
          lt_of_le_of_ne (add_nonneg (e j).val.point_nonnegative.1
            (e j).val.point_nonnegative.2) (Ne.symm zero)
        apply S.positive_width_of_wall_provenance R
          (fun G => ∃ k : Fin n, k < j ∧
            MonotoneStrip.CompletesTail (p k) (tail k) cutoff G) left_wall right_wall member
          (B.enclosingStrip_width_pos (fiveSector_banks_orient_pos positive small i) after_source)
        intro G older same
        obtain ⟨k, earlier, completion⟩ := older
        have different : (e k).val.val ≠ (e j).val.val := by
          intro equal
          have leaf_same : (e k).val = (e j).val := Subtype.ext equal
          have active_same : e k = e j := Subtype.ext leaf_same
          exact (ne_of_lt earlier) (e.injective active_same)
        have avoids := (e k).val.tailGraph.leaf_coordinate_ne (e j).val.property.1
          (e j).val.property.2.1 different (ordered earlier.le)
          ((e j).property.trans_lt (tips_beyond (e k).val (e k).property))
        have at_current : G.coordinate ((p j).re + (p j).im) =
            (tail k).coordinate ((p j).re + (p j).im) :=
          completion.2 _ ⟨ordered earlier.le, (e j).property⟩
        rw [at_current] at same
        exact avoids same
      exact R.insertionGraph_terminalTailsFrom (fun leaf : Leaf => leaf.point)
        (fun leaf => leaf.tailGraph.graph) (e j).val member (e j).val.tailGraph_target
        (e j).property first_strict last_strict target_width trapped)
  refine ⟨T, ?_, ?_, good⟩
  · intro G member
    obtain ⟨j, completion⟩ := provenance G member
    exact ⟨(e j).val, (e j).property, completion⟩
  · intro w active
    obtain ⟨G, member, completion⟩ := represented (e.symm ⟨w, active⟩)
    refine ⟨G, member, ?_⟩
    change MonotoneStrip.CompletesTail (e (e.symm ⟨w, active⟩)).val.point
      (e (e.symm ⟨w, active⟩)).val.tailGraph.graph cutoff G at completion
    have transfer := congrArg (fun a : Active =>
      MonotoneStrip.CompletesTail a.val.point a.val.tailGraph.graph cutoff G)
      (e.apply_symm_apply ⟨w, active⟩)
    exact transfer.mp completion

/-- Retain vertex pinches without the actual terminal-tail witness. -/
theorem exists_geometric_sector_waterfall_vertex_pinches (i : FiveSector) (cutoff : ℝ)
    (tips_beyond : ∀ w : M.GeometricSectorLeaf F covered positive small lower i,
      w.point.re + w.point.im ≤ cutoff →
        cutoff < M.geometricTailEndHeight F covered positive small lower i w.val) :
    let E := insert (0 : ℂ) (Set.range (fun w :
      M.GeometricSectorLeaf F covered positive small lower i => w.point))
    let V := Set.range (fun w : F.GeometricVertex =>
      (fiveSectorFrame t positive small i).place (F.geometricPosition w - K.projectedVertex origin))
    ∃ T : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
      (∀ G ∈ T.separators,
        ∃ w : M.GeometricSectorLeaf F covered positive small lower i,
          w.point.re + w.point.im ≤ cutoff ∧
            MonotoneStrip.CompletesTail w.point w.tailGraph.graph cutoff G) ∧
      (∀ w : M.GeometricSectorLeaf F covered positive small lower i,
        w.point.re + w.point.im ≤ cutoff →
          ∃ G ∈ T.separators,
            MonotoneStrip.CompletesTail w.point w.tailGraph.graph cutoff G) ∧
      ∀ R ∈ T.cells, (R.lower.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧
        R.upper.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧ R.RecoverablePinchesIn E 0 cutoff) ∧
          R.ApproachedPinchesIn V 0 cutoff := by
  obtain ⟨T, provenance, represented, good⟩ :=
    M.exists_geometric_sector_waterfall_with_terminal_tails F covered positive small lower i
      cutoff tips_beyond
  exact ⟨T, provenance, represented, fun R member => ⟨(good R member).1, (good R member).2.1⟩⟩

/-- Retain the reopening-pinch interface without the stronger terminal classification. -/
theorem exists_geometric_sector_waterfall_recoverable (i : FiveSector) (cutoff : ℝ)
    (tips_beyond : ∀ w : M.GeometricSectorLeaf F covered positive small lower i,
      w.point.re + w.point.im ≤ cutoff →
        cutoff < M.geometricTailEndHeight F covered positive small lower i w.val) :
    let E := insert (0 : ℂ) (Set.range (fun w :
      M.GeometricSectorLeaf F covered positive small lower i => w.point))
    ∃ T : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
      (∀ G ∈ T.separators,
        ∃ w : M.GeometricSectorLeaf F covered positive small lower i,
          w.point.re + w.point.im ≤ cutoff ∧
            MonotoneStrip.CompletesTail w.point w.tailGraph.graph cutoff G) ∧
      (∀ w : M.GeometricSectorLeaf F covered positive small lower i,
        w.point.re + w.point.im ≤ cutoff →
          ∃ G ∈ T.separators,
            MonotoneStrip.CompletesTail w.point w.tailGraph.graph cutoff G) ∧
      ∀ R ∈ T.cells, R.lower.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧
        R.upper.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧ R.RecoverablePinchesIn E 0 cutoff := by
  obtain ⟨T, provenance, represented, good⟩ :=
    M.exists_geometric_sector_waterfall_vertex_pinches F covered positive small lower i cutoff
      tips_beyond
  exact ⟨T, provenance, represented, fun R member => (good R member).1⟩

end Unfoldings.ConvexCap.SectorForest
