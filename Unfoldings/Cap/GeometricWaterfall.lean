module

public import Unfoldings.Cap.GeometricSectorData
public import Unfoldings.Geometry.FiniteWaterfall
public import Unfoldings.Topology.HeightEnumeration

/-! Construct a finite strip subdivision from the actual geometric leaves in each sector. -/

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

/-- Process exactly the actual leaves below the cutoff, in increasing height.
The only cutoff condition is that their genuine outer tips lie beyond it. Neither safe
connectors nor covering strips are supplied as hypotheses. Boundary contacts are retained. -/
theorem exists_geometric_sector_waterfall (i : FiveSector) (cutoff : ℝ)
    (tips_beyond : ∀ w : M.GeometricSectorLeaf F covered positive small lower i,
      w.point.re + w.point.im ≤ cutoff →
        cutoff < M.geometricTailEndHeight F covered positive small lower i w.val) :
    ∃ T : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
      (∀ G ∈ T.separators,
        ∃ w : M.GeometricSectorLeaf F covered positive small lower i,
          w.point.re + w.point.im ≤ cutoff ∧
            MonotoneStrip.CompletesTail w.point w.tailGraph.graph cutoff G) ∧
      ∀ w : M.GeometricSectorLeaf F covered positive small lower i,
        w.point.re + w.point.im ≤ cutoff →
          ∃ G ∈ T.separators,
            MonotoneStrip.CompletesTail w.point w.tailGraph.graph cutoff G := by
  let Leaf := M.GeometricSectorLeaf F covered positive small lower i
  let Active := {w : Leaf // w.point.re + w.point.im ≤ cutoff}
  obtain ⟨n, e, ordered⟩ := exists_height_ordered_equiv
    (fun w : Active => w.val.point.re + w.val.point.im)
  let p : Fin n → ℂ := fun j => (e j).val.point
  let tail : Fin n → MonotoneHeightGraph := fun j => (e j).val.tailGraph.graph
  let S := (fiveSectorFrame t positive small i).enclosingStrip
  have sources := (fiveSectorFrame t positive small i).enclosingStrip_source
  obtain ⟨T, provenance, represented⟩ := S.exists_finite_waterfall n p tail cutoff
    sources.1 sources.2 (fun j => (e j).val.point_nonnegative) ordered
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
      (tips_beyond (e k).val (e k).property))
  refine ⟨T, ?_, ?_⟩
  · intro G member
    obtain ⟨j, good⟩ := provenance G member
    exact ⟨(e j).val, (e j).property, good⟩
  · intro w active
    obtain ⟨G, member, good⟩ := represented (e.symm ⟨w, active⟩)
    refine ⟨G, member, ?_⟩
    change MonotoneStrip.CompletesTail (e (e.symm ⟨w, active⟩)).val.point
      (e (e.symm ⟨w, active⟩)).val.tailGraph.graph cutoff G at good
    have transfer := congrArg (fun a : Active =>
      MonotoneStrip.CompletesTail a.val.point a.val.tailGraph.graph cutoff G)
      (e.apply_symm_apply ⟨w, active⟩)
    exact transfer.mp good

end Unfoldings.ConvexCap.SectorForest
