module

public import Unfoldings.Cap.BoundaryTerminalComponent
public import Unfoldings.Cap.SectorBankRays

/-! Extreme disappearing runs in neighboring sectors select the same actual radial component. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0}

/-- Different maximum heights and different terminal contour copies are
retained. Only their genuine radial component is identified across the shared ray. -/
theorem adjacent_boundary_run_maxima_same_component
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {i j : FiveSector} (shared : fiveSectorFirst t i = fiveSectorLast t j)
    {ε cutoff physicalRadius radius : ℝ} {n m : ℕ}
    (first_cells : Fin (n + 1) → MonotoneStrip)
    (last_cells : Fin (m + 1) → MonotoneStrip)
    (first_traces : ∀ k, R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i
        (first_cells k) ε cutoff)
    (last_traces : ∀ k, R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) j
        (last_cells k) ε cutoff)
    (first_contacts : ∀ k : Fin n, Set.EqOn (first_cells k.castSucc).upper.point
      (first_cells k.succ).lower.point (Set.Icc 0 cutoff))
    (last_contacts : ∀ k : Fin m, Set.EqOn (last_cells k.castSucc).upper.point
      (last_cells k.succ).lower.point (Set.Icc 0 cutoff))
    (first_terminals : ∀ k, B.EmptyCircleContinuation i (first_traces k) physicalRadius radius)
    (last_terminals : ∀ k, B.EmptyCircleContinuation j (last_traces k) physicalRadius radius)
    (first_tails : ∀ k, (first_cells k).TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    (last_tails : ∀ k, (last_cells k).TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small lower j => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    (a : Fin (n + 1)) (b : Fin (m + 1))
    (first_highest : ∀ k, (first_terminals k).height ≤ (first_terminals a).height)
    (last_highest : ∀ k, (last_terminals k).height ≤ (last_terminals b).height)
    (first_outer : Set.EqOn (first_cells (Fin.last n)).upper.point
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff))
    (last_outer : Set.EqOn (fiveSectorFrame t positive small j).enclosingStrip.lower.point
      (last_cells 0).lower.point (Set.Icc 0 cutoff)) :
    ∃ c : F.Component,
      Q.projectedVertex (first_terminals a).vertex ∈ (F.componentTail c).carrier ∧
      Q.projectedVertex (last_terminals b).vertex ∈ (F.componentTail c).carrier ∧
      ∀ e : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
        M.cutPieceLabel F covered (Sum.inl e) ≠ c := by
  obtain ⟨c, first_member, unattached⟩ := last_run_maximum_on_unattached_component R D B
    first_cells first_traces first_contacts first_terminals first_tails deep a first_highest
    first_outer
  obtain ⟨d, last_member, _⟩ := first_run_maximum_on_unattached_component R D B
    last_cells last_traces last_contacts last_terminals last_tails deep b last_highest last_outer
  have first_bank : (fiveSectorFrame t positive small i).place
      (Q.projectedVertex (first_terminals a).vertex - K.projectedVertex origin) =
        (fiveSectorFrame t positive small i).enclosingStrip.upper.point
          (first_terminals a).height := by
    rw [← (first_terminals a).physical, add_sub_cancel_left, LinearIsometryEquiv.apply_symm_apply]
    exact B.last_run_maximum_on_upper_bank i first_cells first_traces first_contacts first_terminals
      a first_highest first_outer
  have last_bank : (fiveSectorFrame t positive small j).place
      (Q.projectedVertex (last_terminals b).vertex - K.projectedVertex origin) =
        (fiveSectorFrame t positive small j).enclosingStrip.lower.point
          (last_terminals b).height := by
    rw [← (last_terminals b).physical, add_sub_cancel_left, LinearIsometryEquiv.apply_symm_apply]
    exact (B.first_run_maximum_on_lower_bank j last_cells last_traces last_contacts last_terminals
      b last_highest last_outer).symm
  have same := F.component_eq_on_shared_sector_bank positive small lower shared
    (first_terminals a).height_bounds.1 (last_terminals b).height_bounds.1
    first_member last_member first_bank last_bank
  subst d
  exact ⟨c, first_member, last_member, unattached⟩

end Unfoldings.ConvexCap.SectorForest
