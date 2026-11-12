module

public import Unfoldings.Cap.BoundaryRunSourceBankCandidate
public import Unfoldings.Cap.BoundaryRunLateCirclePhysicalCandidate

/-! A source bank candidate is strictly inside the circle or has the exact physical crossing. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {i : FiveSector}

variable
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    (leaf_vertices : ∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (footprint : Q.footprint = K.clipFootprint Z) {cutoff : ℝ}
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision) {ε : ℝ}
    (traces : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      R.RadialStripTraceData positive small D
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i cell.val ε cutoff)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (budget : FineC.totalInteriorAngularDefect Set.univ < Real.pi)
    (nonnegative : 0 ≤ ε) (small_error : ε < 1 / 2)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement Q
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference)
        (fiveSectorFrame t positive small i).place f).linear z - z‖ ≤ ε * ‖z‖)
    (pinches : ∀ cell : {S : MonotoneStrip // S ∈ P.cells}, cell.val.ApproachedPinchesIn
      (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
          M.extendedGeometricCuts F} =>
        (fiveSectorFrame t positive small i).place
          (Q.projectedVertex v.val - K.projectedVertex origin))) 0 cutoff)

variable {n : ℕ} (cells : Fin (n + 1) → {S : MonotoneStrip // S ∈ P.cells})
  (contacts : ∀ j : Fin n, Set.EqOn (cells j.castSucc).val.upper.point
    (cells j.succ).val.lower.point (Set.Icc 0 cutoff))
  (ordered_cells : ∀ a b : Fin (n + 1), a < b → List.Sublist [cells a, cells b] P.cells.attach)
  {physicalRadius radius : ℝ}
  (terminals : ∀ j, B.EmptyCircleContinuation i (traces (cells j)) physicalRadius radius)
  (tails : ∀ j, (cells j).val.TerminalTailsFrom
    (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
    (fun leaf => leaf.tailGraph.graph) cutoff)

variable
  (provenance : ∀ H ∈ P.separators,
    ∃ leaf : M.GeometricSectorLeaf F covered positive small lower i,
      leaf.point.re + leaf.point.im ≤ cutoff ∧
        MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
  (represented : ∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
    leaf.point.re + leaf.point.im ≤ cutoff → ∃ H ∈ P.separators,
      MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
  (leaf_coherent : ∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
    D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
  (source : {S : MonotoneStrip // S ∈ P.cells})
  (slice : source.val.BankCircleSlice (traces source).value (traces source).center cutoff radius)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
  (outside : radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
  (outside_empty : ∀ k, radius ∉ (traces (cells k)).emptyCircleExceptions)
  (empty : ∀ k, (traces (cells k)).value '' (cells k).val.openSlab 0 cutoff ∩
    {z | ‖z - (traces (cells k)).center‖ = radius} = ∅)

include outward leaf_vertices footprint deep curvature_covered budget nonnegative
  small_error linear_error pinches contacts ordered_cells tails provenance represented
  leaf_coherent radius_positive far outside outside_empty empty

theorem exists_boundary_run_source_bank_candidate_with_physical (pivot : Fin (n + 1))
    (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (physical_room : physicalRadius ≤ cutoff) (upper : Bool)
    (strict_extreme : if upper then
      ∀ k, pivot < k → (terminals k).height < (terminals pivot).height
      else ∀ k, k < pivot → (terminals k).height < (terminals pivot).height)
    (source_order : if upper then ∀ k, List.Sublist [source, cells k] P.cells.attach
      else ∀ k, List.Sublist [cells k, source] P.cells.attach)
    (facing : if upper then
      Set.EqOn source.val.upper.point (cells 0).val.lower.point (Set.Icc 0 cutoff)
      else Set.EqOn source.val.lower.point (cells (Fin.last n)).val.upper.point (Set.Icc 0 cutoff))
    (separator : if upper then source.val.upper ∈ P.separators else source.val.lower ∈ P.separators)
    (outer : if upper then
      Set.EqOn (cells (Fin.last n)).val.upper.point
        (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff)
      else Set.EqOn (fiveSectorFrame t positive small i).enclosingStrip.lower.point
        (cells 0).val.lower.point (Set.Icc 0 cutoff)) :
    let z := if upper then source.val.upper.point slice.upperHeight
      else source.val.lower.point slice.lowerHeight
    let coordinate : ℂ → ℝ := if upper then Complex.re else Complex.im
    ∃ c : F.Component,
      Q.projectedVertex (terminals pivot).vertex ∈ (F.componentTail c).carrier ∧
      (∀ e : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
        M.cutPieceLabel F covered (Sum.inl e) ≠ c) ∧
      ∃ e : {v : FineC.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots},
        Q.projectedVertex e.val ∈ (F.componentTail c).carrier ∧ ∃ s : unitInterval,
        (((traces (cells pivot)).outputFrame.symm
            ((traces (cells pivot)).value
              ((cells pivot).val.lower.point (terminals pivot).height)) =
          (if upper then R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))
            else R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ))) ∨
          ((terminals pivot).height < (if upper then slice.upperHeight else slice.lowerHeight) ∧
            (traces source).outputFrame.symm ((traces source).value z) =
              (if upper then R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))
                else R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ)))))) ∧
        coordinate ((traces source).value z - (traces source).center) ≤
          coordinate (B.sectorFrame i
            ((if upper then R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))
              else R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ))) -
              D.projectedMap Q (K.projectedVertex origin))) ∧
        ‖(if upper then R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))
            else R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ))) -
          D.projectedMap Q (K.projectedVertex origin)‖ ≤ radius ∧
        (‖(if upper then R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))
            else R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ))) -
            D.projectedMap Q (K.projectedVertex origin)‖ < radius ∨
          K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm z =
            AffineMap.lineMap (Q.projectedVertex e.val)
              (Q.projectedVertex (R.spanningCompletion.parents.parent e.val)) (s : ℝ)) := by
  let z := if upper then source.val.upper.point slice.upperHeight
    else source.val.lower.point slice.lowerHeight
  let coordinate : ℂ → ℝ := if upper then Complex.re else Complex.im
  let h := if upper then slice.upperHeight else slice.lowerHeight
  have center : (traces source).center = B.sectorFrame i
      (D.projectedMap Q (K.projectedVertex origin)) := (traces source).center_eq_outputFrame
  by_cases early : h ≤ (terminals pivot).height
  · obtain ⟨c, member, unattached, e, child, s, matching, inside⟩ :=
      exists_boundary_run_terminal_bank_candidate R outward D B (fun k => (cells k).val)
        (fun k => traces (cells k)) contacts terminals tails pivot highest upper strict_extreme
        outer
        (pinches (cells pivot)) footprint deep physical_room leaf_vertices leaf_coherent
    have bound : coordinate ((traces source).value z - (traces source).center) ≤
        coordinate (B.sectorFrame i
          ((if upper then R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))
            else R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ))) -
            D.projectedMap Q (K.projectedVertex origin))) := by
      cases upper
      · dsimp only [coordinate, z]
        have initial := early_lower_circle_im_le_any_run_maximum_of_contacts R outward D B
          leaf_vertices footprint deep P traces curvature_covered budget nonnegative small_error.le
          linear_error pinches cells contacts ordered_cells terminals tails provenance represented
          leaf_coherent source slice radius_positive far outside outside_empty empty pivot highest
          source_order facing separator early
        rw [matching] at initial
        simpa only [center, map_sub, Complex.sub_im, Bool.false_eq_true, ↓reduceIte] using
          sub_le_sub_right initial
            (B.sectorFrame i (D.projectedMap Q (K.projectedVertex origin))).im
      · dsimp only [coordinate, z]
        have initial := early_upper_circle_re_le_any_run_maximum_of_contacts R outward D B
          leaf_vertices footprint deep P traces curvature_covered budget nonnegative small_error.le
          linear_error pinches cells contacts ordered_cells terminals tails provenance represented
          leaf_coherent source slice radius_positive far outside outside_empty empty pivot highest
          source_order facing separator early
        rw [matching] at initial
        simpa only [center, map_sub, Complex.sub_re, Bool.false_eq_true, ↓reduceIte] using
          sub_le_sub_right initial
            (B.sectorFrame i (D.projectedMap Q (K.projectedVertex origin))).re
    have origin : (traces (cells pivot)).outputFrame.symm
        ((traces (cells pivot)).value ((cells pivot).val.lower.point (terminals pivot).height)) =
        (if upper then R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))
          else R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ))) := by
      change (B.sectorFrame i).symm _ = _
      rw [matching, LinearIsometryEquiv.symm_apply_apply]
    exact ⟨c, member, unattached, e, child, s, Or.inl origin, bound, inside.le, Or.inl inside⟩
  · obtain ⟨c, member, unattached, e, child, s, physical, matching, size⟩ :=
      exists_boundary_run_late_circle_candidate_with_physical R outward D B (fun k => (cells k).val)
        (fun k => traces (cells k)) contacts terminals tails pivot highest footprint deep
        physical_room
        leaf_vertices leaf_coherent upper outer radius_positive small_error far (traces source)
        slice
        facing (not_le.mp early).le outside
    have framed := congrArg (traces source).outputFrame matching
    rw [LinearIsometryEquiv.apply_symm_apply] at framed
    have actual_value : (traces source).value z = B.sectorFrame i
        (if upper then R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))
          else R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ))) := framed
    refine ⟨c, member, unattached, e, child, s, Or.inr ⟨not_le.mp early, matching⟩, ?_, size.le,
      Or.inr physical⟩
    rw [actual_value, center, ← map_sub]

end Unfoldings.ConvexCap.SectorForest
