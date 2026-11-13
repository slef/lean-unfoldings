module

public import Unfoldings.Roof.BoundaryTerminalSectorAssignment
public import Unfoldings.Roof.RadialComponentSeed
public import Unfoldings.Roof.RadialComponentFineAncestry
public import Unfoldings.Roof.RadialComponentIncomingBank
public import Unfoldings.Geometry.RadialTailHeightOrder

/-! Boundary terminals are reached from coherent fine seeds of their radial components. -/

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

theorem boundary_terminal_has_coherent_seed_ancestor
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S : MonotoneStrip} {ε cutoff physicalRadius radius : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (tails : S.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    (terminal : B.EmptyCircleContinuation i data physicalRadius radius)
    (footprint : Q.footprint = outerDomain)
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (physical_room : physicalRadius ≤ cutoff)
    (leaf_vertices : ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (leaf_coherent : ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    (H : MonotoneHeightGraph)
    (wall : H = (fiveSectorFrame t positive small i).enclosingStrip.lower ∨
      H = (fiveSectorFrame t positive small i).enclosingStrip.upper)
    (agreement : Set.EqOn H.point S.lower.point (Set.Icc terminal.height cutoff)) :
    ∃ c : F.Component, ∃ w : FineC.Vertex Set.univ,
      Q.projectedVertex w = F.componentSeed c ∧
      D.ProjectedCoherentAt Q (Q.projectedVertex w) ∧
      Q.projectedVertex w ∈ (F.componentTail c).carrier ∧
      Q.projectedVertex terminal.vertex ∈ (F.componentTail c).carrier ∧
      (∀ e : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
        M.cutPieceLabel F covered (Sum.inl e) ≠ c) ∧
      R.spanningCompletion.parents.Ancestor w terminal.vertex := by
  obtain ⟨leaf, after_leaf, _, _, member, unattached⟩ := boundary_terminal_leaf_component R D B
    data tails terminal deep H wall agreement
  let c := M.geometricComponent F covered leaf.val
  obtain ⟨w, at_seed, coherent, seed_member⟩ := M.fine_coherent_seed_of_unattached_leaf F covered
    positive small c unattached leaf rfl Q D (leaf_vertices leaf) (leaf_coherent leaf)
  have geometric_seed := M.unattached_component_nonroot_position_eq_seed F covered
    positive small c unattached leaf.val leaf.property.1 rfl
  have at_leaf : Q.projectedVertex w = F.geometricPosition leaf.val :=
    at_seed.trans geometric_seed.symm
  let frame := (fiveSectorFrame t positive small i).place
  let height : Plane →ₗ[ℝ] ℝ :=
    (Complex.reCLM.toLinearMap + Complex.imCLM.toLinearMap).comp frame.toLinearMap
  have inside : Q.projectedVertex w - origin ∈ closedFiveSector t i := by
    rw [at_leaf]
    exact leaf.component_positions leaf.val rfl
  have terminal_bank : frame (Q.projectedVertex terminal.vertex - origin) =
      H.point terminal.height := by
    rw [← terminal.physical, add_sub_cancel_left, frame.apply_symm_apply]
    exact (agreement ⟨le_rfl, terminal.height_bounds.2.le⟩).symm
  have terminal_height : height (Q.projectedVertex terminal.vertex - origin) =
      terminal.height := by
    change (frame _).re + (frame _).im = _
    rw [terminal_bank]
    exact H.point_height terminal.height
  have start : height (Q.projectedVertex w - origin) ≤
      height (Q.projectedVertex terminal.vertex - origin) := by
    rw [terminal_height, at_leaf]
    exact after_leaf
  have terminal_internal : Q.projectedVertex terminal.vertex ∈ interior (outerDomain) := by
    apply deep
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact terminal.physical_inside.le.trans physical_room
  have not_tip : Q.projectedVertex terminal.vertex ≠ (F.componentTail c).tip := by
    intro equal
    exact (F.componentTail c).boundary.2 (equal ▸ terminal_internal)
  have tip_inside := (F.componentTail c).position_inDirectionWedge_of_mem seed_member inside
    (F.componentTail c).tip_mem
  have tip_ne : (F.componentTail c).tip - origin ≠ 0 := by
    intro zero
    exact (F.componentTail c).boundary.2 ((sub_eq_zero.mp zero).symm ▸
      F.encloses (interior_subset F.origin))
  have quadrant := (fiveSectorFrame t positive small i).quadrant_self tip_inside tip_ne
  have height_positive : 0 < height ((F.componentTail c).tip - origin) :=
    add_pos quadrant.1 quadrant.2
  have finish := (F.componentTail c).linear_height_lt_tip_of_mem_ne height height_positive
    member not_tip
  have ancestor := M.unattached_component_vertex_ancestor F covered R w terminal.vertex c
    unattached seed_member positive small outward footprint i inside member start finish
  exact ⟨c, w, at_seed, coherent, seed_member, member, unattached, ancestor⟩

theorem boundary_terminal_coherent_or_incoming_bank
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S : MonotoneStrip} {ε cutoff physicalRadius radius : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (tails : S.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    (terminal : B.EmptyCircleContinuation i data physicalRadius radius)
    (footprint : Q.footprint = outerDomain)
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (physical_room : physicalRadius ≤ cutoff)
    (leaf_vertices : ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (leaf_coherent : ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    (H : MonotoneHeightGraph)
    (wall : H = (fiveSectorFrame t positive small i).enclosingStrip.lower ∨
      H = (fiveSectorFrame t positive small i).enclosingStrip.upper)
    (agreement : Set.EqOn H.point S.lower.point (Set.Icc terminal.height cutoff)) :
    D.ProjectedCoherentAt Q (Q.projectedVertex terminal.vertex) ∨
      ∃ c : F.Component,
        (∀ e : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
          M.cutPieceLabel F covered (Sum.inl e) ≠ c) ∧
        Q.projectedVertex terminal.vertex ∈ (F.componentTail c).carrier ∧
        ∃ e : {v : FineC.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots},
          R.spanningCompletion.parents.parent e.val = terminal.vertex ∧
          Q.projectedVertex e.val ∈ M.extendedGeometricCuts F ∧
          Q.projectedVertex (R.spanningCompletion.parents.parent e.val) -
            Q.projectedVertex e.val ∈ closedFiveSector t i ∧
          Q.projectedVertex e.val ∈ (F.componentTail c).carrier ∧
          ∃ b ∈ Set.Ioo (0 : ℝ) terminal.height,
            origin + (fiveSectorFrame t positive small i).place.symm (H.point b) =
              Q.projectedVertex e.val := by
  obtain ⟨c, w, _, coherent, seed_member, member, unattached, ancestor⟩ :=
    boundary_terminal_has_coherent_seed_ancestor R outward D B data tails terminal footprint deep
      physical_room leaf_vertices leaf_coherent H wall agreement
  by_cases same : w = terminal.vertex
  · exact Or.inl (same ▸ coherent)
  right
  have terminal_internal : Q.projectedVertex terminal.vertex ∈ interior Q.footprint := by
    rw [footprint]
    apply deep
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact terminal.physical_inside.le.trans physical_room
  have nonroot : terminal.vertex ∉ R.spanningCompletion.parents.roots := by
    intro root
    have boundary := (Set.ext_iff.mp R.spanningCompletion.roots_eq _).mp root
    exact (Q.projectedVertex_mem_interior_iff terminal.vertex).mp terminal_internal boundary
  let frame := fiveSectorFrame t positive small i
  have terminal_bank : frame.place
      (Q.projectedVertex terminal.vertex - origin) = H.point terminal.height := by
    rw [← terminal.physical, add_sub_cancel_left, frame.place.apply_symm_apply]
    exact (agreement ⟨le_rfl, terminal.height_bounds.2.le⟩).symm
  obtain ⟨upper, which⟩ : ∃ upper : Bool,
      H = if upper then frame.enclosingStrip.upper else frame.enclosingStrip.lower := by
    rcases wall with lower_bank | upper_bank
    · exact ⟨false, lower_bank⟩
    · exact ⟨true, upper_bank⟩
  have terminal_inside : Q.projectedVertex terminal.vertex - origin ∈
      closedFiveSector t i := by
    have banks := fiveSector_enclosingStrip_bank_closed positive small i terminal.height_bounds.1.le
    have physical : Q.projectedVertex terminal.vertex - origin =
        frame.place.symm (H.point terminal.height) := by
      rw [← terminal_bank, frame.place.symm_apply_apply]
    rw [physical, which]
    cases upper
    · exact banks.1
    · exact banks.2
  have inside := (F.componentTail c).position_inDirectionWedge_of_mem member terminal_inside
    seed_member
  have on_bank : frame.place
      (Q.projectedVertex terminal.vertex - origin) =
        (if upper then frame.enclosingStrip.upper else frame.enclosingStrip.lower).point
          terminal.height := by rw [← which]; exact terminal_bank
  obtain ⟨e, parent, reaches, on_cuts, direction, b, bounds, point⟩ :=
    M.unattached_component_incoming_boundary_bank F covered R w terminal.vertex c
      unattached seed_member member positive small outward i inside nonroot ancestor same upper
      terminal.height_bounds.1 on_bank
  have child_member := M.unattached_component_nonroot_ancestor_position F covered R w c
    unattached seed_member e reaches
  rw [← which] at point
  exact ⟨c, unattached, member, e, parent, on_cuts, direction, child_member, b, bounds, point⟩

end Unfoldings.ConvexRoof.SectorForest
