module

public import Unfoldings.Cap.GeometricWaterfall
public import Unfoldings.Cap.GeometricBankPersistence
public import Unfoldings.Cap.StrictGeometricTailGraphs
public import Unfoldings.Geometry.RecoverableWaterfall

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
  let Leaf := M.GeometricSectorLeaf F covered positive small lower i
  let E := insert (0 : ℂ) (Set.range (fun w : Leaf => w.point))
  let Active := {w : Leaf // w.point.re + w.point.im ≤ cutoff}
  obtain ⟨n, e, ordered⟩ := exists_height_ordered_equiv
    (fun w : Active => w.val.point.re + w.val.point.im)
  let p : Fin n → ℂ := fun j => (e j).val.point
  let tail : Fin n → MonotoneHeightGraph := fun j => (e j).val.tailGraph.graph
  let B := fiveSectorFrame t positive small i
  let S := B.enclosingStrip
  have sources := B.enclosingStrip_source
  have initial : S.lower.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧
      S.upper.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧ S.RecoverablePinchesIn E 0 cutoff := by
    refine ⟨(B.enclosingStrip_strictCoordinatesOn _).1,
      (B.enclosingStrip_strictCoordinatesOn _).2, ?_⟩
    intro h slab same k later width
    exact Or.inl (B.enclosingStrip_recoverablePinchesIn cutoff h slab same k later width)
  obtain ⟨T, provenance, represented, good⟩ := S.exists_finite_waterfall_recoverable n p tail
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

end Unfoldings.ConvexCap.SectorForest
