module

public import Unfoldings.Cap.BoundaryRunCircleComponent
public import Unfoldings.Cap.BoundaryTerminalSeedAncestor
public import Unfoldings.Cap.SharedSectorBankCoordinates
public import Unfoldings.Cap.RadialComponentCircleBanks
public import Unfoldings.Cap.CrossFrameTraceQuadrants

/-! A neighboring surviving boundary circle supplies its actual bank candidate automatically. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {i j : FiveSector}

theorem exists_boundary_run_neighbor_circle_candidate
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
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
      (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    (pivot : Fin (n + 1)) (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (footprint : Q.footprint = K.clipFootprint Z)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    (physical_room : physicalRadius ≤ cutoff)
    (leaf_vertices : ∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (leaf_coherent : ∀ a, ∀ leaf : M.GeometricSectorLeaf F covered positive small lower a,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    (upper : Bool)
    (shared : if upper then fiveSectorFirst t i = fiveSectorLast t j
      else fiveSectorFirst t j = fiveSectorLast t i)
    (outer : if upper then
      Set.EqOn (cells (Fin.last n)).upper.point
        (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff)
      else Set.EqOn (fiveSectorFrame t positive small i).enclosingStrip.lower.point
        (cells 0).lower.point (Set.Icc 0 cutoff))
    (radius_positive : 0 < radius) (small_error : ε < 1 / 2)
    (room : 2 * radius < (1 / 2 - ε) * cutoff)
    (outside : ∀ k, radius ∉ (traces k).emptyCircleExceptions)
    (empty : ∀ k, (traces k).value '' (cells k).openSlab 0 cutoff ∩
      {z | ‖z - (traces k).center‖ = radius} = ∅)
    {T : MonotoneStrip}
    (other : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) j T ε cutoff)
    (slice : T.BankCircleSlice other.value other.center cutoff radius)
    (neighbor_outer : if upper then
      Set.EqOn T.lower.point (fiveSectorFrame t positive small j).enclosingStrip.lower.point
        (Set.Icc 0 cutoff)
      else Set.EqOn T.upper.point (fiveSectorFrame t positive small j).enclosingStrip.upper.point
        (Set.Icc 0 cutoff))
    (outside_vertices : radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small) :
    let z := if upper then T.lower.point slice.lowerHeight else T.upper.point slice.upperHeight
    ∃ c : F.Component,
      Q.projectedVertex (terminals pivot).vertex ∈ (F.componentTail c).carrier ∧
      (∀ e : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
        M.cutPieceLabel F covered (Sum.inl e) ≠ c) ∧
      ∃ e : {v : FineC.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots},
        Q.projectedVertex e.val ∈ (F.componentTail c).carrier ∧ ∃ s : unitInterval,
        other.outputFrame.symm (other.value z) =
          (if upper then R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ))
            else R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))) ∧
        ‖(if upper then R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ))
            else R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))) -
          D.projectedMap Q (K.projectedVertex origin)‖ = radius := by
  let frame := fiveSectorFrame t positive small i
  let otherFrame := fiveSectorFrame t positive small j
  let H := if upper then frame.enclosingStrip.upper else frame.enclosingStrip.lower
  let J := if upper then otherFrame.enclosingStrip.lower else otherFrame.enclosingStrip.upper
  let k := if upper then slice.lowerHeight else slice.upperHeight
  let z := if upper then T.lower.point slice.lowerHeight else T.upper.point slice.upperHeight
  have far : radius < (1 / 2 - ε) * cutoff := by linarith
  have heights := other.circle_slice_heights radius_positive far slice
  have k_bounds : k ∈ Set.Ioo 0 cutoff := by
    cases upper
    · exact heights.2
    · exact heights.1
  have at_root : z = J.point k := by
    cases upper
    · exact neighbor_outer ⟨heights.2.1.le, heights.2.2.le⟩
    · exact neighbor_outer ⟨heights.1.1.le, heights.1.2.le⟩
  have closed : z ∈ closure other.strictDomain := by
    cases upper
    · change T.upper.point slice.upperHeight ∈ closure other.strictDomain
      exact slice.upper_closed
    · change T.lower.point slice.lowerHeight ∈ closure other.strictDomain
      exact slice.lower_closed
  have size : ‖other.value z - other.center‖ = radius := by
    cases upper
    · change ‖other.value (T.upper.point slice.upperHeight) - other.center‖ = radius
      exact slice.upper_radius
    · change ‖other.value (T.lower.point slice.lowerHeight) - other.center‖ = radius
      exact slice.lower_radius
  let z' := frame.place (otherFrame.place.symm z)
  let h := z'.re + z'.im
  have converted : 0 < h ∧ z' = H.point h := by
    cases upper
    · change 0 < (frame.place (otherFrame.place.symm z)).re +
          (frame.place (otherFrame.place.symm z)).im ∧
        frame.place (otherFrame.place.symm z) = frame.enclosingStrip.lower.point
          ((frame.place (otherFrame.place.symm z)).re + (frame.place (otherFrame.place.symm z)).im)
      rw [at_root]
      exact fiveSector_shared_upper_to_lower_coordinates positive small shared k_bounds.1
    · change 0 < (frame.place (otherFrame.place.symm z)).re +
          (frame.place (otherFrame.place.symm z)).im ∧
        frame.place (otherFrame.place.symm z) = frame.enclosingStrip.upper.point
          ((frame.place (otherFrame.place.symm z)).re + (frame.place (otherFrame.place.symm z)).im)
      rw [at_root]
      exact fiveSector_shared_lower_to_upper_coordinates positive small shared k_bounds.1
  have region := other.closed_circle_point_mem_sectorSweepInterior small_error closed size room
  have before : h < cutoff := by
    have bound := region i
    simpa only [add_sub_cancel_left] using bound
  have contact : frame.place.symm (H.point h) = otherFrame.place.symm z := by
    have inverse := congrArg frame.place.symm converted.2
    rw [frame.place.symm_apply_apply] at inverse
    exact inverse.symm
  obtain ⟨c, terminal_member, circle_member, _, unattached⟩ :=
    boundary_run_circle_on_terminal_component R D B cells traces contacts terminals tails pivot
      highest deep leaf_coherent upper outer radius_positive outside empty other closed size
      ⟨converted.1, before⟩ contact
  have wall : H = frame.enclosingStrip.lower ∨ H = frame.enclosingStrip.upper := by
    cases upper
    · exact Or.inl rfl
    · exact Or.inr rfl
  have agreement : Set.EqOn H.point (cells pivot).lower.point
      (Set.Icc (terminals pivot).height cutoff) := by
    cases upper
    · exact B.first_run_lower_tail_on_boundary i cells traces contacts terminals pivot highest outer
    · intro a member
      exact (B.last_run_lower_tail_on_boundary i cells traces contacts terminals pivot highest
        outer member).symm
  obtain ⟨d, w, at_seed, _, seed_member, terminal_at_seed, unattached_seed, _⟩ :=
    boundary_terminal_has_coherent_seed_ancestor R outward D B (traces pivot) (tails pivot)
      (terminals pivot) footprint deep physical_room leaf_vertices (leaf_coherent i) H wall
      agreement
  have same : c = d := F.component_eq_of_pos_scaled_positions lower terminal_member
    terminal_at_seed
    zero_lt_one (by simp only [one_smul])
  have member : K.projectedVertex origin + otherFrame.place.symm z ∈
      (F.componentTail d).carrier :=
    (congrArg (fun a => (F.componentTail a).carrier) same).subset circle_member
  have cone : otherFrame.place.symm z ∈ closedFiveSector t j := by
    rw [at_root]
    have banks := fiveSector_enclosingStrip_bank_closed positive small j k_bounds.1.le
    cases upper
    · exact banks.2
    · exact banks.1
  have inside : Q.projectedVertex w - K.projectedVertex origin ∈ closedFiveSector t j := by
    have actual_cone :
        K.projectedVertex origin + otherFrame.place.symm z - K.projectedVertex origin ∈
        closedFiveSector t j := by simpa only [add_sub_cancel_left] using cone
    exact (F.componentTail d).position_inDirectionWedge_of_mem member actual_cone seed_member
  cases upper
  · obtain ⟨a, s, child, matching, at_radius⟩ := M.upper_circle_bank_on_component_in_sweep F covered
      lower R outward D B w d unattached_seed at_seed footprint j inside other slice radius_positive
      far outside_vertices small_error deep member
    exact ⟨d, terminal_at_seed, unattached_seed, R.completedBankChain w a, child, s,
      matching, at_radius⟩
  · obtain ⟨a, s, child, matching, at_radius⟩ := M.lower_circle_bank_on_component_in_sweep F covered
      lower R outward D B w d unattached_seed at_seed footprint j inside other slice radius_positive
      far outside_vertices small_error deep member
    exact ⟨d, terminal_at_seed, unattached_seed, R.completedBankChain w a, child, s,
      matching, at_radius⟩

end Unfoldings.ConvexCap.SectorForest
