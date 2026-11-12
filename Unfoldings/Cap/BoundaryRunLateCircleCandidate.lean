module

public import Unfoldings.Cap.BoundaryTerminalSeedAncestor
public import Unfoldings.Cap.RadialComponentCircleBanks

/-! Crossings after maximal boundary-run terminals supply exact actual circle-bank candidates. -/

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

theorem exists_boundary_run_late_circle_candidate
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
    (leaf_coherent : ∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    (upper : Bool)
    (outer : if upper then
      Set.EqOn (cells (Fin.last n)).upper.point
        (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff)
      else Set.EqOn (fiveSectorFrame t positive small i).enclosingStrip.lower.point
        (cells 0).lower.point (Set.Icc 0 cutoff))
    (radius_positive : 0 < radius) (small_error : ε < 1 / 2)
    (far : radius < (1 / 2 - ε) * cutoff)
    {S : MonotoneStrip}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (slice : S.BankCircleSlice data.value data.center cutoff radius)
    (facing : if upper then Set.EqOn S.upper.point (cells 0).lower.point (Set.Icc 0 cutoff)
      else Set.EqOn S.lower.point (cells (Fin.last n)).upper.point (Set.Icc 0 cutoff))
    (late : (terminals pivot).height ≤ if upper then slice.upperHeight else slice.lowerHeight)
    (outside_vertices : radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small) :
    let z := if upper then S.upper.point slice.upperHeight else S.lower.point slice.lowerHeight
    ∃ c : F.Component,
      Q.projectedVertex (terminals pivot).vertex ∈ (F.componentTail c).carrier ∧
      (∀ e : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
        M.cutPieceLabel F covered (Sum.inl e) ≠ c) ∧
      ∃ e : {v : FineC.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots},
        Q.projectedVertex e.val ∈ (F.componentTail c).carrier ∧ ∃ s : unitInterval,
        data.outputFrame.symm (data.value z) =
          (if upper then R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))
            else R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ))) ∧
        ‖(if upper then R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))
            else R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ))) -
          D.projectedMap Q (K.projectedVertex origin)‖ = radius := by
  let frame := fiveSectorFrame t positive small i
  let H := if upper then frame.enclosingStrip.upper else frame.enclosingStrip.lower
  let h := if upper then slice.upperHeight else slice.lowerHeight
  let z := if upper then S.upper.point slice.upperHeight else S.lower.point slice.lowerHeight
  have heights := data.circle_slice_heights radius_positive far slice
  have height : h ∈ Set.Ioo 0 cutoff := by
    cases upper
    · exact heights.1
    · exact heights.2
  have collapsed (k : Fin (n + 1)) : (cells k).lower.coordinate h = (cells k).upper.coordinate h :=
    (terminals k).merged h ⟨(highest k).trans late, height.2.le⟩
  have coordinates := MonotoneStrip.collapsed_chain_points_of_contacts cells
    (fun k => congrArg Complex.re (contacts k ⟨height.1.le, height.2.le⟩)) collapsed
    0 (Fin.last n)
  have at_root : z = H.point h := by
    cases upper
    · exact (facing ⟨height.1.le, height.2.le⟩).trans
        ((coordinates.symm).trans (outer ⟨height.1.le, height.2.le⟩).symm)
    · exact (facing ⟨height.1.le, height.2.le⟩).trans
        (coordinates.trans (outer ⟨height.1.le, height.2.le⟩))
  have wall : H = frame.enclosingStrip.lower ∨ H = frame.enclosingStrip.upper := by
    cases upper
    · exact Or.inl rfl
    · exact Or.inr rfl
  have agreement : Set.EqOn H.point (cells pivot).lower.point
      (Set.Icc (terminals pivot).height cutoff) := by
    cases upper
    · exact B.first_run_lower_tail_on_boundary i cells traces contacts terminals pivot highest outer
    · intro k member
      exact (B.last_run_lower_tail_on_boundary i cells traces contacts terminals pivot highest
        outer member).symm
  obtain ⟨leaf, after_leaf, _, follows, terminal_member, unattached⟩ :=
    boundary_terminal_leaf_component R D B (traces pivot) (tails pivot) (terminals pivot) deep H
      wall agreement
  let c := M.geometricComponent F covered leaf.val
  let x := K.projectedVertex origin + frame.place.symm z
  have on_component : x ∈ (F.componentTail c).carrier := by
    rcases lt_or_eq_of_le late with after | equal
    · have at_point : frame.place (x - K.projectedVertex origin) =
          leaf.tailGraph.graph.point h := by
        dsimp only [x]
        rw [add_sub_cancel_left, frame.place.apply_symm_apply, at_root]
        exact (agreement ⟨late, height.2.le⟩).trans (follows h ⟨late, height.2.le⟩).1
      have boundary : x - K.projectedVertex origin ∉ strictFiveSector t i := by
        dsimp only [x]
        rw [add_sub_cancel_left, at_root]
        have banks := fiveSector_enclosingStrip_bank_not_strict_any positive small i height.1.le
        cases upper
        · exact banks.1 i
        · exact banks.2 i
      exact leaf.tail_bank_contact_radial at_point (after_leaf.trans_lt after)
        (height.2.trans (leaf.tail_end_beyond_clip_ball deep)) boundary
    · change (terminals pivot).height = h at equal
      have actual : x = Q.projectedVertex (terminals pivot).vertex := by
        dsimp only [x]
        rw [at_root, ← equal, agreement ⟨le_rfl, (terminals pivot).height_bounds.2.le⟩]
        exact (terminals pivot).physical
      exact actual.symm ▸ terminal_member
  obtain ⟨d, w, at_seed, _, seed_member, terminal_at_seed, unattached_seed, _⟩ :=
    boundary_terminal_has_coherent_seed_ancestor R outward D B (traces pivot) (tails pivot)
      (terminals pivot) footprint deep physical_room leaf_vertices leaf_coherent H wall agreement
  have same : c = d := F.component_eq_of_pos_scaled_positions lower terminal_member
    terminal_at_seed
    zero_lt_one (by simp only [one_smul])
  have member : x ∈ (F.componentTail d).carrier :=
    (congrArg (fun a => (F.componentTail a).carrier) same).subset on_component
  have inside : Q.projectedVertex w - K.projectedVertex origin ∈ closedFiveSector t i := by
    have banks := fiveSector_enclosingStrip_bank_closed positive small i height.1.le
    have cone : x - K.projectedVertex origin ∈ closedFiveSector t i := by
      dsimp only [x]
      rw [add_sub_cancel_left, at_root]
      cases upper
      · exact banks.1
      · exact banks.2
    exact (F.componentTail d).position_inDirectionWedge_of_mem member cone seed_member
  cases upper
  · obtain ⟨a, s, child, matching, size⟩ := M.lower_circle_bank_on_component_in_sweep F covered
      lower R outward D B w d unattached_seed at_seed footprint i inside data slice
      radius_positive far
      outside_vertices small_error deep member
    exact ⟨d, terminal_at_seed, unattached_seed, R.completedBankChain w a, child, s, matching, size⟩
  · obtain ⟨a, s, child, matching, size⟩ := M.upper_circle_bank_on_component_in_sweep F covered
      lower R outward D B w d unattached_seed at_seed footprint i inside data slice
      radius_positive far
      outside_vertices small_error deep member
    exact ⟨d, terminal_at_seed, unattached_seed, R.completedBankChain w a, child, s, matching, size⟩

end Unfoldings.ConvexCap.SectorForest
