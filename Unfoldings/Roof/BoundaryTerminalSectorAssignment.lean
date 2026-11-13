module

public import Unfoldings.Roof.SameSectorEmptyCircleComparison
public import Unfoldings.Roof.SectorBoundaryComponents
public import Unfoldings.Roof.GeometricTailBankContacts
public import Unfoldings.Cap.BoundaryRunTerminalPoint

/-! A boundary terminal retains the unique assigned sector of its actual radial component. -/

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

/-- Agreement on the terminal suffix is physical. The proof also covers a
terminal exactly at its geometric leaf height, without evaluating developed
trace values on any later collapsed bank. -/
theorem boundary_terminal_leaf_component
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S : MonotoneStrip} {ε cutoff physicalRadius radius : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (tails : S.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    (continuation : B.EmptyCircleContinuation i data physicalRadius radius)
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (H : MonotoneHeightGraph)
    (wall : H = (fiveSectorFrame t positive small i).enclosingStrip.lower ∨
      H = (fiveSectorFrame t positive small i).enclosingStrip.upper)
    (agreement : Set.EqOn H.point S.lower.point (Set.Icc continuation.height cutoff)) :
    ∃ leaf : M.GeometricSectorLeaf F covered positive small i,
      leaf.point.re + leaf.point.im ≤ continuation.height ∧
      (fiveSectorFrame t positive small i).place
        (Q.projectedVertex continuation.vertex - origin) =
          leaf.tailGraph.graph.point continuation.height ∧
      (∀ h ∈ Set.Icc continuation.height cutoff,
        S.lower.point h = leaf.tailGraph.graph.point h ∧
          S.upper.point h = leaf.tailGraph.graph.point h) ∧
      Q.projectedVertex continuation.vertex ∈
        (F.componentTail (M.geometricComponent F covered leaf.val)).carrier ∧
      ∀ e : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
        M.cutPieceLabel F covered (Sum.inl e) ≠ M.geometricComponent F covered leaf.val := by
  obtain ⟨leaf, after_leaf, same_start, follows⟩ :=
    terminal_geometric_tail R D B data tails continuation
  let frame := (fiveSectorFrame t positive small i).place
  have boundary (h : ℝ) (nonnegative : 0 ≤ h) :
      ∀ j, frame.symm (H.point h) ∉ strictFiveSector t j := by
    have banks := fiveSector_enclosingStrip_bank_not_strict_any positive small i nonnegative
    rcases wall with equal | equal
    · exact equal.symm ▸ banks.1
    · exact equal.symm ▸ banks.2
  let h := (continuation.height + cutoff) / 2
  have above : continuation.height < h := by dsimp only [h]; linarith [continuation.height_bounds.2]
  have below : h < cutoff := by dsimp only [h]; linarith [continuation.height_bounds.2]
  have interval : h ∈ Set.Icc continuation.height cutoff := ⟨above.le, below.le⟩
  let x := origin + frame.symm (H.point h)
  have at_point : frame (x - origin) = leaf.tailGraph.graph.point h := by
    dsimp only [x]
    rw [add_sub_cancel_left, frame.apply_symm_apply]
    exact (agreement interval).trans (follows h interval).1
  have x_boundary : ∀ j, x - origin ∉ strictFiveSector t j := by
    dsimp only [x]
    rw [add_sub_cancel_left]
    exact boundary h (continuation.height_bounds.1.le.trans above.le)
  have radial := leaf.tail_bank_contact_radial at_point (after_leaf.trans_lt above)
    (below.trans (leaf.tail_end_beyond_clip_ball deep)) (x_boundary i)
  have unattached := M.sector_boundary_component_unattached positive small F covered
    radial x_boundary
  refine ⟨leaf, after_leaf, same_start, follows, ?_, unattached⟩
  have terminal_bank : Q.projectedVertex continuation.vertex - origin =
      frame.symm (H.point continuation.height) := by
    rw [← continuation.physical, add_sub_cancel_left,
      agreement ⟨le_rfl, continuation.height_bounds.2.le⟩]
  by_cases after : leaf.point.re + leaf.point.im < continuation.height
  · exact leaf.tail_bank_contact_radial same_start after
      (continuation.height_bounds.2.trans (leaf.tail_end_beyond_clip_ball deep))
      (terminal_bank ▸ boundary continuation.height continuation.height_bounds.1.le i)
  · have equal_height : continuation.height = leaf.point.re + leaf.point.im :=
      le_antisymm (le_of_not_gt after) after_leaf
    have point : leaf.tailGraph.graph.point (leaf.point.re + leaf.point.im) = leaf.point :=
      leaf.tailGraph.graph.point_eq_of_coordinate leaf.point leaf.tailGraph_target
    have physical : Q.projectedVertex continuation.vertex = F.geometricPosition leaf.val := by
      have shifted : Q.projectedVertex continuation.vertex - origin =
          F.geometricPosition leaf.val - origin := by
        apply frame.injective
        rw [same_start, equal_height, point]
        rfl
      exact sub_left_injective shifted
    rw [physical]
    exact M.unattached_component_positions_on_tail F covered _ unattached leaf.val rfl

theorem boundary_terminal_on_assigned_component
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S : MonotoneStrip} {ε cutoff physicalRadius radius : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (tails : S.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    (continuation : B.EmptyCircleContinuation i data physicalRadius radius)
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (H : MonotoneHeightGraph)
    (wall : H = (fiveSectorFrame t positive small i).enclosingStrip.lower ∨
      H = (fiveSectorFrame t positive small i).enclosingStrip.upper)
    (agreement : Set.EqOn H.point S.lower.point (Set.Icc continuation.height cutoff)) :
    ∃ c : F.Component, Q.projectedVertex continuation.vertex ∈ (F.componentTail c).carrier ∧
      (M.geometricComponentSector F covered positive small c).sector = i ∧
      ∀ e : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
        M.cutPieceLabel F covered (Sum.inl e) ≠ c := by
  obtain ⟨leaf, _, _, _, member, unattached⟩ := boundary_terminal_leaf_component R D B data tails
    continuation deep H wall agreement
  exact ⟨M.geometricComponent F covered leaf.val, member, leaf.property.2.2, unattached⟩

variable {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
  {Q : ConvexCap FineC}
  (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
  (D : FacewiseDevelopment FineC R.retain)
  (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
  {ε cutoff physicalRadius radius : ℝ} {n : ℕ}
  (cells : Fin (n + 1) → MonotoneStrip)
  (traces : ∀ j, R.RadialStripTraceData positive small D
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i (cells j) ε cutoff)
  (contacts : ∀ j : Fin n, Set.EqOn (cells j.castSucc).upper.point
    (cells j.succ).lower.point (Set.Icc 0 cutoff))
  (terminals : ∀ j, B.EmptyCircleContinuation i (traces j) physicalRadius radius)
  (tails : ∀ j, (cells j).TerminalTailsFrom
    (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
    (fun leaf => leaf.tailGraph.graph) cutoff)
  (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))

include contacts tails deep

/-- The highest actual terminal of an initial disappearing run belongs to
one unattached radial component, derived from the enclosing physical ray. -/
theorem first_run_maximum_on_assigned_component
    (pivot : Fin (n + 1)) (highest : ∀ j, (terminals j).height ≤ (terminals pivot).height)
    (outer : Set.EqOn (fiveSectorFrame t positive small i).enclosingStrip.lower.point
      (cells 0).lower.point (Set.Icc 0 cutoff)) :
    ∃ c : F.Component, Q.projectedVertex (terminals pivot).vertex ∈ (F.componentTail c).carrier ∧
      (M.geometricComponentSector F covered positive small c).sector = i ∧
      ∀ e : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
        M.cutPieceLabel F covered (Sum.inl e) ≠ c := by
  exact boundary_terminal_on_assigned_component R D B (traces pivot) (tails pivot)
    (terminals pivot) deep _ (Or.inl rfl)
    (B.first_run_lower_tail_on_boundary i cells traces contacts terminals pivot highest outer)

/-- The final disappearing run has the corresponding genuine radial component. -/
theorem last_run_maximum_on_assigned_component
    (pivot : Fin (n + 1)) (highest : ∀ j, (terminals j).height ≤ (terminals pivot).height)
    (outer : Set.EqOn (cells (Fin.last n)).upper.point
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff)) :
    ∃ c : F.Component, Q.projectedVertex (terminals pivot).vertex ∈ (F.componentTail c).carrier ∧
      (M.geometricComponentSector F covered positive small c).sector = i ∧
      ∀ e : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
        M.cutPieceLabel F covered (Sum.inl e) ≠ c := by
  exact boundary_terminal_on_assigned_component R D B (traces pivot) (tails pivot)
    (terminals pivot) deep _ (Or.inr rfl)
    (fun _ member => (B.last_run_lower_tail_on_boundary i cells traces contacts terminals
      pivot highest outer member).symm)

end Unfoldings.ConvexRoof.SectorForest
