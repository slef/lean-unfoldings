module

public import Unfoldings.Cap.BoundaryRunNeighborCirclePhysicalCandidate
public import Unfoldings.Topology.ClosedCompactWitness
public import Unfoldings.Cap.ClosedBankPropertyLimit
public import Unfoldings.Cap.ClosedBankCircleCrossing
public import Unfoldings.Cap.ClosedEmptyCircleRunRadiusGap
public import Unfoldings.Cap.TerminalHeightUniqueness
public import Unfoldings.Cap.RadialClosedCircleSections
public import Unfoldings.Cap.RadialComponentCirclePhysicalBanks

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

theorem exists_closed_section_boundary_neighbor_candidate
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
    (empty : ∀ k, (traces k).value '' closure ((cells k).openSlab 0 cutoff) ∩
      {z | ‖z - (traces k).center‖ = radius} = ∅)
    (continuations : ∀ r ∈ Set.Ioo 0 radius, ∀ k,
      r ∉ (traces k).emptyCircleExceptions →
      (traces k).value '' (cells k).openSlab 0 cutoff ∩
        {z | ‖z - (traces k).center‖ = r} = ∅ →
      Nonempty (B.EmptyCircleContinuation i (traces k) physicalRadius r))
    {T : MonotoneStrip}
    (other : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) j T ε cutoff)
    (slice : T.ClosedBankCircleSection other.value other.center cutoff radius)
    (neighbor_outer : if upper then
      Set.EqOn T.lower.point (fiveSectorFrame t positive small j).enclosingStrip.lower.point
        (Set.Icc 0 cutoff)
      else Set.EqOn T.upper.point (fiveSectorFrame t positive small j).enclosingStrip.upper.point
        (Set.Icc 0 cutoff))
    (pinches : T.ApproachedPinchesIn
      (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
          M.extendedGeometricCuts F} =>
        (fiveSectorFrame t positive small j).place
          (Q.projectedVertex v.val - K.projectedVertex origin))) 0 cutoff)
    {μ : ℝ} (close_margin : ε < μ)
    (margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im) :
    let z := if upper then T.lower.point slice.lowerHeight else T.upper.point slice.upperHeight
    ∃ c : F.Component,
      Q.projectedVertex (terminals pivot).vertex ∈ (F.componentTail c).carrier ∧
      (∀ e : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
        M.cutPieceLabel F covered (Sum.inl e) ≠ c) ∧
      ∃ e : {v : FineC.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots},
        Q.projectedVertex e.val ∈ (F.componentTail c).carrier ∧ ∃ s : unitInterval,
        K.projectedVertex origin + (fiveSectorFrame t positive small j).place.symm z =
          AffineMap.lineMap (Q.projectedVertex e.val)
            (Q.projectedVertex (R.spanningCompletion.parents.parent e.val)) (s : ℝ) ∧
        other.outputFrame.symm (other.value z) =
          (if upper then R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ))
            else R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))) ∧
        ‖(if upper then R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ))
            else R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))) -
          D.projectedMap Q (K.projectedVertex origin)‖ = radius := by
  classical
  let := F.finite
  let := RadialTailFamily.finiteComponent F.tail
  let H := if upper then T.lower else T.upper
  let h := if upper then slice.lowerHeight else slice.upperHeight
  let bank := fun (e : {v : FineC.Vertex Set.univ //
      v ∉ R.spanningCompletion.parents.roots}) (s : unitInterval) =>
    if upper then R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ))
      else R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))
  let relation := fun (q : F.Component × {v : FineC.Vertex Set.univ //
      v ∉ R.spanningCompletion.parents.roots}) (k : ℝ) (s : unitInterval) =>
    Q.projectedVertex (terminals pivot).vertex ∈ (F.componentTail q.1).carrier ∧
      (∀ e : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
        M.cutPieceLabel F covered (Sum.inl e) ≠ q.1) ∧
      Q.projectedVertex q.2.val ∈ (F.componentTail q.1).carrier ∧
      K.projectedVertex origin + (fiveSectorFrame t positive small j).place.symm (H.point k) =
        AffineMap.lineMap (Q.projectedVertex q.2.val)
          (Q.projectedVertex (R.spanningCompletion.parents.parent q.2.val)) (s : ℝ) ∧
      other.outputFrame.symm (other.value (H.point k)) = bank q.2 s
  have relation_closed (q) : IsClosed {p : ℝ × unitInterval | relation q p.1 p.2} := by
    have physical_closed : IsClosed {p : ℝ × unitInterval |
        K.projectedVertex origin + (fiveSectorFrame t positive small j).place.symm
          (H.point p.1) = AffineMap.lineMap (Q.projectedVertex q.2.val)
            (Q.projectedVertex (R.spanningCompletion.parents.parent q.2.val)) (p.2 : ℝ)} :=
      isClosed_eq (continuous_const.add
        ((fiveSectorFrame t positive small j).place.symm.continuous.comp
          (H.point_continuous.comp continuous_fst)))
        (AffineMap.lineMap_continuous.comp (continuous_subtype_val.comp continuous_snd))
    have bank_continuous : Continuous (fun p : ℝ × unitInterval => bank q.2 p.2) := by
      dsimp only [bank]
      split_ifs <;> dsimp only [RadialCutForest.parentEntrancePoint,
        RadialCutForest.parentExitPoint] <;> fun_prop
    have value_closed := isClosed_eq
      (other.outputFrame.symm.continuous.comp (other.continuous.comp
        (H.point_continuous.comp continuous_fst))) bank_continuous
    by_cases allowed : Q.projectedVertex (terminals pivot).vertex ∈
        (F.componentTail q.1).carrier ∧
        (∀ e : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
          M.cutPieceLabel F covered (Sum.inl e) ≠ q.1) ∧
        Q.projectedVertex q.2.val ∈ (F.componentTail q.1).carrier
    · have sets_equal : {p : ℝ × unitInterval | relation q p.1 p.2} =
          {p : ℝ × unitInterval |
            K.projectedVertex origin + (fiveSectorFrame t positive small j).place.symm
                (H.point p.1) = AffineMap.lineMap (Q.projectedVertex q.2.val)
                  (Q.projectedVertex (R.spanningCompletion.parents.parent q.2.val)) (p.2 : ℝ) ∧
              other.outputFrame.symm (other.value (H.point p.1)) = bank q.2 p.2} := by
        ext p
        exact ⟨fun member => member.2.2.2,
          fun member => ⟨allowed.1, allowed.2.1, allowed.2.2, member⟩⟩
      rw [sets_equal]
      exact physical_closed.inter value_closed
    · have none : {p : ℝ × unitInterval | relation q p.1 p.2} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro p member
        exact allowed ⟨member.1, member.2.1, member.2.2.1⟩
      rw [none]
      exact isClosed_empty
  have property_closed := isClosed_exists_finite_compact relation relation_closed
  have wall : H = T.lower ∨ H = T.upper := by
    cases upper
    · exact Or.inr rfl
    · exact Or.inl rfl
  have height : h ∈ Set.Icc 0 cutoff := by
    cases upper
    · exact slice.upper_bounds
    · exact slice.lower_bounds
  have closed : H.point h ∈ closure other.strictDomain := by
    cases upper
    · exact slice.upper_closed
    · exact slice.lower_closed
  have size : ‖other.value (H.point h) - other.center‖ = radius := by
    cases upper
    · exact slice.upper_radius
    · exact slice.lower_radius
  have far : radius < (1 / 2 - ε) * cutoff := by linarith
  obtain ⟨lower_radius, lower_nonnegative, lower_lt, absent⟩ :=
    RadialCutForest.exists_common_inner_radius_of_empty_closed_circles traces
      radius_positive far empty
  let exception := D.fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small ∪
    ⋃ k : Fin (n + 1), (traces k).emptyCircleExceptions
  have finite : exception.Finite :=
    (D.finite_fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference)
      positive small).union (Set.finite_iUnion fun k => (traces k).finite_emptyCircleExceptions)
  obtain ⟨_, active⟩ := closure_nonempty_iff.mp ⟨_, closed⟩
  have source_value : other.value (H.point 0) = other.center := by
    cases upper
    · exact (other.source_bank_values active).2
    · exact (other.source_bank_values active).1
  have regular : ∀ r ∈ Set.Ioo lower_radius radius, r ∉ exception →
      ∃ k ∈ Set.Icc 0 cutoff, H.point k ∈ closure other.strictDomain ∧
        ‖other.value (H.point k) - other.center‖ = r ∧ ∃ q s, relation q k s := by
    intro r bounds outside
    have r_bounds : r ∈ Set.Ioo 0 radius :=
      ⟨lower_nonnegative.trans_lt bounds.1, bounds.2⟩
    have far_r := bounds.2.trans far
    have room_r : 2 * r < (1 / 2 - ε) * cutoff := by linarith [bounds.2]
    have outside_vertices : r ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small :=
      fun member => outside (Or.inl member)
    have outside_empty (k : Fin (n + 1)) : r ∉ (traces k).emptyCircleExceptions :=
      fun member => outside (Or.inr (Set.mem_iUnion.mpr ⟨k, member⟩))
    have empty_open (k : Fin (n + 1)) :
        (traces k).value '' (cells k).openSlab 0 cutoff ∩
          {z | ‖z - (traces k).center‖ = r} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨⟨z, member, rfl⟩, size⟩
      have belongs : (traces k).value z ∈
          (traces k).value '' closure ((cells k).openSlab 0 cutoff) ∩
            {z | ‖z - (traces k).center‖ = r} :=
        ⟨⟨z, subset_closure member, rfl⟩, size⟩
      rw [absent r bounds.1 k] at belongs
      exact belongs
    let nearby := fun k => Classical.choice
      (continuations r r_bounds k (outside_empty k) (empty_open k))
    have heights (k) : (nearby k).height = (terminals k).height :=
      (nearby k).height_eq (terminals k)
    have highest_r (k) : (nearby k).height ≤ (nearby pivot).height := by
      rw [heights k, heights pivot]
      exact highest k
    have positions : Q.projectedVertex (nearby pivot).vertex =
        Q.projectedVertex (terminals pivot).vertex := by
      rw [← (nearby pivot).physical, ← (terminals pivot).physical, heights pivot]
    obtain ⟨k, _, k_closed, k_size⟩ :=
      other.exists_closed_bank_point_on_smaller_circle H wall height.1 closed size r_bounds
    have approached := other.closed_circle_point_mem_closure_openSlab r_bounds.1 far_r
      k_closed k_size
    obtain ⟨r_slice⟩ := other.circle_slice_of_approached_point_off_vertexRadii
      pinches close_margin margin r_bounds.1 far_r outside_vertices approached k_size
    obtain ⟨c, member, unattached, e, child, s, physical, matching, _⟩ :=
      exists_boundary_run_neighbor_circle_candidate_with_physical R outward D B cells traces
        contacts nearby tails pivot highest_r footprint deep physical_room leaf_vertices
          leaf_coherent
        upper shared outer r_bounds.1 small_error room_r outside_empty empty_open other r_slice
        neighbor_outer outside_vertices
    rw [positions] at member
    cases upper
    · refine ⟨r_slice.upperHeight, r_slice.upper_bounds, r_slice.upper_closed,
        r_slice.upper_radius, (c, e), s, ?_⟩
      exact ⟨member, unattached, child, physical, matching⟩
    · refine ⟨r_slice.lowerHeight, r_slice.lower_bounds, r_slice.lower_closed,
        r_slice.lower_radius, (c, e), s, ?_⟩
      exact ⟨member, unattached, child, physical, matching⟩
  obtain ⟨⟨c, e⟩, s, member, unattached, child, physical, matching⟩ :=
    other.radial.closed_bank_property_at_radius_limit other.continuous H wall source_value
      height.1 radius_positive closed size lower_lt finite property_closed regular
  have at_radius : ‖bank e s - D.projectedMap Q (K.projectedVertex origin)‖ = radius := by
    rw [← matching, other.outputFrame_symm_source_distance]
    exact size
  have point_eq : H.point h =
      (if upper then T.lower.point slice.lowerHeight else T.upper.point slice.upperHeight) := by
    cases upper <;> rfl
  refine ⟨c, member, unattached, e, child, s, ?_, ?_, at_radius⟩
  · simpa only [point_eq] using physical
  · simpa only [point_eq] using matching

end Unfoldings.ConvexCap.SectorForest
