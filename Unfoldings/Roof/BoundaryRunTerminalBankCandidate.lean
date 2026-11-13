module

public import Unfoldings.Roof.SectorBankRays

public import Unfoldings.Roof.BoundaryTerminalSeedAncestor
public import Unfoldings.Cap.BoundaryRunIncomingBankMatching
public import Unfoldings.Cap.BoundaryTerminalMargins
public import Unfoldings.Cap.CoherentParentBankPoints

/-! Every extreme boundary-run terminal supplies an actual inner bank candidate. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outerDomain : Set Plane} {F : K.SkirtTailFamily outerDomain (origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {i : FiveSector}

theorem exists_boundary_run_terminal_bank_candidate
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {ε cutoff physicalRadius radius : ℝ} {n : ℕ}
    (cells : Fin (n + 1) → MonotoneStrip)
    (traces : ∀ k, R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i (cells k) ε cutoff)
    (contacts : ∀ k : Fin n, Set.EqOn (cells k.castSucc).upper.point
      (cells k.succ).lower.point (Set.Icc 0 cutoff))
    (terminals : ∀ k, B.EmptyCircleContinuation i (traces k) physicalRadius radius)
    (tails : ∀ k, (cells k).TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    (pivot : Fin (n + 1)) (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (upper : Bool)
    (strict_extreme : if upper then
      ∀ k, pivot < k → (terminals k).height < (terminals pivot).height
      else ∀ k, k < pivot → (terminals k).height < (terminals pivot).height)
    (outer : if upper then
      Set.EqOn (cells (Fin.last n)).upper.point
        (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff)
      else Set.EqOn (fiveSectorFrame t positive small i).enclosingStrip.lower.point
        (cells 0).lower.point (Set.Icc 0 cutoff))
    (pinches : (cells pivot).ApproachedPinchesIn
      (Set.range (fun w : {w : FineC.Vertex Set.univ // Q.projectedVertex w ∈
          M.extendedGeometricCuts F} =>
        (fiveSectorFrame t positive small i).place
          (Q.projectedVertex w.val - origin))) 0 cutoff)
    (footprint : Q.footprint = outerDomain)
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (physical_room : physicalRadius ≤ cutoff)
    (leaf_vertices : ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (leaf_coherent : ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val)) :
    ∃ c : F.Component,
      Q.projectedVertex (terminals pivot).vertex ∈ (F.componentTail c).carrier ∧
      (∀ e : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
        M.cutPieceLabel F covered (Sum.inl e) ≠ c) ∧
      ∃ e : {v : FineC.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots},
        Q.projectedVertex e.val ∈ (F.componentTail c).carrier ∧ ∃ s : unitInterval,
        (traces pivot).value ((cells pivot).lower.point (terminals pivot).height) =
          B.sectorFrame i (if upper then
            R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))
            else R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ))) ∧
        ‖(if upper then R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))
            else R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ))) -
          D.projectedMap Q (origin)‖ < radius := by
  let frame := fiveSectorFrame t positive small i
  let H := if upper then frame.enclosingStrip.upper else frame.enclosingStrip.lower
  have wall : H = frame.enclosingStrip.lower ∨ H = frame.enclosingStrip.upper := by
    cases upper
    · exact Or.inl rfl
    · exact Or.inr rfl
  have agreement : Set.EqOn H.point (cells pivot).lower.point
      (Set.Icc (terminals pivot).height cutoff) := by
    cases upper
    · exact B.first_run_lower_tail_on_boundary i cells traces contacts terminals pivot highest outer
    · intro h member
      exact (B.last_run_lower_tail_on_boundary i cells traces contacts terminals pivot highest
        outer member).symm
  obtain ⟨leaf, _, _, _, terminal_member, unattached⟩ := boundary_terminal_leaf_component R D B
    (traces pivot) (tails pivot) (terminals pivot) deep H wall agreement
  let c := M.geometricComponent F covered leaf.val
  have in_clip : Q.projectedVertex (terminals pivot).vertex ∈ interior Q.footprint := by
    rw [footprint]
    apply deep
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (terminals pivot).physical_inside.le.trans physical_room
  have nonroot : (terminals pivot).vertex ∉ R.spanningCompletion.parents.roots := by
    intro root
    exact (Q.projectedVertex_mem_interior_iff _).mp in_clip
      ((Set.ext_iff.mp R.spanningCompletion.roots_eq _).mp root)
  rcases boundary_terminal_coherent_or_incoming_bank R outward D B (traces pivot) (tails pivot)
    (terminals pivot) footprint deep physical_room leaf_vertices leaf_coherent H wall agreement with
    coherent | incoming
  · let e : {v : FineC.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots} :=
      ⟨(terminals pivot).vertex, nonroot⟩
    have included : (cells pivot).openSlab 0 cutoff ⊆ (traces pivot).strictDomain :=
      fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
    have closed := closure_mono included (terminals pivot).lower_closed
    have physical_coherent : D.ProjectedCoherentAt Q
        (origin + frame.place.symm
          ((cells pivot).lower.point (terminals pivot).height)) := by
      rw [(terminals pivot).physical]
      exact coherent
    have value := (traces pivot).physical_value_of_closed_coherent closed physical_coherent
    rw [(terminals pivot).physical] at value
    have banks := R.parent_bank_child_eq_of_coherent D e coherent
    have matching : (traces pivot).value ((cells pivot).lower.point (terminals pivot).height) =
        B.sectorFrame i (if upper then R.parentExitPoint (R.completedDevelopment D) e 1
          else R.parentEntrancePoint (R.completedDevelopment D) e 1) := by
      cases upper
      · rw [banks.1]
        exact value
      · rw [banks.2]
        exact value
    have actual_matching : (traces pivot).value
        ((cells pivot).lower.point (terminals pivot).height) =
        B.sectorFrame i (if upper then
          R.parentExitPoint (R.completedDevelopment D) e (1 - ((0 : unitInterval) : ℝ))
          else R.parentEntrancePoint (R.completedDevelopment D) e
            (1 - ((0 : unitInterval) : ℝ))) := by
      simpa only [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero] using matching
    exact ⟨c, terminal_member, unattached, e, terminal_member, 0, actual_matching,
      B.terminal_actual_point_norm_lt i (traces pivot) (terminals pivot) _ actual_matching⟩
  · obtain ⟨d, _, other_member, e, parent, on_cuts, direction, child, b, bounds, bank⟩ := incoming
    have same : d = c := F.component_eq_of_pos_scaled_positions other_member terminal_member
      zero_lt_one (by simp only [one_smul])
    have child_member : Q.projectedVertex e.val ∈ (F.componentTail c).carrier :=
      (congrArg (fun a => (F.componentTail a).carrier) same).subset child
    have matching : (traces pivot).value ((cells pivot).lower.point (terminals pivot).height) =
        B.sectorFrame i (if upper then R.parentExitPoint (R.completedDevelopment D) e 0
          else R.parentEntrancePoint (R.completedDevelopment D) e 0) := by
      cases upper
      · exact B.first_run_maximum_matches_incoming_entrance i cells traces contacts terminals pivot
          pinches e on_cuts direction parent bounds.1.le bounds.2 strict_extreme outer bank
      · exact B.last_run_maximum_matches_incoming_exit i cells traces contacts terminals pivot
          pinches e on_cuts direction parent bounds.1.le bounds.2 strict_extreme outer bank
    have actual_matching : (traces pivot).value
        ((cells pivot).lower.point (terminals pivot).height) =
        B.sectorFrame i (if upper then
          R.parentExitPoint (R.completedDevelopment D) e (1 - ((1 : unitInterval) : ℝ))
          else R.parentEntrancePoint (R.completedDevelopment D) e
            (1 - ((1 : unitInterval) : ℝ))) := by
      simpa only [show ((1 : unitInterval) : ℝ) = 1 from rfl, sub_self] using matching
    exact ⟨c, terminal_member, unattached, e, child_member, 1, actual_matching,
      B.terminal_actual_point_norm_lt i (traces pivot) (terminals pivot) _ actual_matching⟩

end Unfoldings.ConvexRoof.SectorForest
