module

public import Unfoldings.Roof.SectorBankRays

public import Unfoldings.Cap.BoundaryRunCirclePrefix
public import Unfoldings.Roof.BoundaryTerminalSectorAssignment
public import Unfoldings.Cap.EnclosingBankSegments

/-! Neighboring boundary-circle crossings lie on the terminal's actual radial component. -/

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

theorem boundary_run_circle_on_terminal_component
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain)
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
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (leaf_coherent : ∀ a, ∀ leaf : M.GeometricSectorLeaf F covered positive small a,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    (upper : Bool)
    (outer : if upper then
      Set.EqOn (cells (Fin.last n)).upper.point
        (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff)
      else Set.EqOn (fiveSectorFrame t positive small i).enclosingStrip.lower.point
        (cells 0).lower.point (Set.Icc 0 cutoff))
    (radius_positive : 0 < radius)
    (outside : ∀ k, radius ∉ (traces k).emptyCircleExceptions)
    (empty : ∀ k, (traces k).value '' (cells k).openSlab 0 cutoff ∩
      {w | ‖w - (traces k).center‖ = radius} = ∅)
    {otherCalibration : Plane ≃ₗᵢ[ℝ] ℂ} {j : FiveSector} {T : MonotoneStrip} {δ limit : ℝ}
    (other : R.RadialStripTraceData positive small D otherCalibration j T δ limit)
    {z : ℂ} (closed : z ∈ closure other.strictDomain)
    (size : ‖other.value z - other.center‖ = radius)
    {h : ℝ} (height : h ∈ Set.Ioo 0 cutoff)
    (contact : (fiveSectorFrame t positive small i).place.symm
        ((if upper then (fiveSectorFrame t positive small i).enclosingStrip.upper
          else (fiveSectorFrame t positive small i).enclosingStrip.lower).point h) =
      (fiveSectorFrame t positive small j).place.symm z) :
    ∃ c : F.Component,
      Q.projectedVertex (terminals pivot).vertex ∈ (F.componentTail c).carrier ∧
      origin + (fiveSectorFrame t positive small j).place.symm z ∈
        (F.componentTail c).carrier ∧
      (M.geometricComponentSector F covered positive small c).sector = i ∧
      ∀ e : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
        M.cutPieceLabel F covered (Sum.inl e) ≠ c := by
  let frame := fiveSectorFrame t positive small i
  let H := if upper then frame.enclosingStrip.upper else frame.enclosingStrip.lower
  let x := origin + frame.place.symm (H.point h)
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
    boundary_terminal_leaf_component R D B (traces pivot) (tails pivot) (terminals pivot)
      deep H wall agreement
  let c := M.geometricComponent F covered leaf.val
  have boundary : ∀ a, x - origin ∉ strictFiveSector t a := by
    dsimp only [x]
    rw [add_sub_cancel_left]
    have banks := fiveSector_enclosingStrip_bank_not_strict_any positive small i height.1.le
    cases upper
    · exact banks.1
    · exact banks.2
  have alternative : (terminals pivot).height < h ∨ ¬ D.ProjectedCoherentAt Q x := by
    cases upper
    · exact B.first_run_circle_after_terminal_or_not_coherent i cells traces contacts terminals
        pivot radius_positive outside empty other closed size height.1 outer contact
    · exact B.last_run_circle_after_terminal_or_not_coherent i cells traces contacts terminals
        pivot radius_positive outside empty other closed size height.1 outer contact
  have radial : x ∈ (F.componentTail c).carrier := by
    rcases alternative with after | not_coherent
    · have interval : h ∈ Set.Icc (terminals pivot).height cutoff := ⟨after.le, height.2.le⟩
      have at_point : frame.place (x - origin) =
          leaf.tailGraph.graph.point h := by
        dsimp only [x]
        rw [add_sub_cancel_left, frame.place.apply_symm_apply]
        exact (agreement interval).trans (follows h interval).1
      exact leaf.tail_bank_contact_radial at_point (after_leaf.trans_lt after)
        (height.2.trans (leaf.tail_end_beyond_clip_ball deep)) (boundary i)
    · rcases M.sector_boundary_coherent_or_skirt positive small F covered R D
        leaf_coherent boundary with coherent | ⟨d, member⟩
      · exact (not_coherent coherent).elim
      · let a := h / (terminals pivot).height
        have positive_scale : 0 < a := div_pos height.1 (terminals pivot).height_bounds.1
        have product : a * (terminals pivot).height = h :=
          div_mul_cancel₀ _ (terminals pivot).height_bounds.1.ne'
        have homogeneous : H.point (a * (terminals pivot).height) =
            a • H.point (terminals pivot).height := by
          cases upper
          · exact frame.enclosingStrip_lower_point_smul positive_scale.le
              (terminals pivot).height_bounds.1.le
          · exact frame.enclosingStrip_upper_point_smul positive_scale.le
              (terminals pivot).height_bounds.1.le
        have scaled : H.point h = a • H.point (terminals pivot).height :=
          (congrArg H.point product.symm).trans homogeneous
        have terminal_point :
            Q.projectedVertex (terminals pivot).vertex - origin =
            frame.place.symm (H.point (terminals pivot).height) := by
          rw [agreement ⟨le_rfl, (terminals pivot).height_bounds.2.le⟩,
            ← (terminals pivot).physical, add_sub_cancel_left]
        have scale : x - origin =
            a • (Q.projectedVertex (terminals pivot).vertex - origin) := by
          dsimp only [x]
          rw [add_sub_cancel_left, terminal_point, scaled, map_smul]
        have same := F.component_eq_of_pos_scaled_positions terminal_member member
          positive_scale scale
        exact (congrArg (fun d => (F.componentTail d).carrier) same).symm.subset member
  have actual_x : x = origin +
      (fiveSectorFrame t positive small j).place.symm z := congrArg
    (fun p : Plane => origin + p) contact
  exact ⟨c, terminal_member, actual_x ▸ radial, leaf.property.2.2, unattached⟩

end Unfoldings.ConvexRoof.SectorForest
