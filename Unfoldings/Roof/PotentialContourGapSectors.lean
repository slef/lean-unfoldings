module

public import Unfoldings.Roof.PotentialContourGap
public import Unfoldings.Roof.CurvatureNonnegative
public import Unfoldings.Complex.AngleCutSums
public import Unfoldings.Complex.BoundaryChainLeftAperture
public import Unfoldings.Geometry.SourceRotationSector
public import Unfoldings.Geometry.OrientedBankGapBendChart

/-! Angular charts at the tip and bends of an actual saved contour gap. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.PotentialCutForest

open Real
open scoped NNReal ENNReal

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {f : Plane → ℝ} {cuts : Set Plane} (R : K.PotentialCutForest f cuts)
  (Q : C.BoundaryContour (C.selectedRetain R.selection))
  (starts : C.contourOriginalVertex R.selection Q 0 ∈ R.parents.roots)
  (event : C.PositiveContourSource R.selection Q)

local notation "Length" => C.positiveContourBankLength R.selection Q event
local notation "Source" => C.positiveContourVertex R.selection Q event
local notation "Defect" => C.interiorAngularDefect Set.univ Source

local notation "Retain" =>
  C.processedParentRetain R.selection (C.contourFrontier R.selection Q event.val.succ)
local notation "Chain" => R.contourSourceBankChain Q starts event
local notation "Bank" => R.contourSourceRay Q starts event
local notation "Opened" => R.contourSourceOpenedRay Q starts event

/-- Interior points of the saved bank have the full original ambient angle bound. -/
theorem contourSource_first_bend_aperture (k : Fin Length) (outward : (Bank).Outward)
    (strict : 0 < inner ℝ ((Bank).chain.vertex k.succ.castSucc - (Bank).start) ((Bank).chain.edge k.succ)) :
    radialLeftCornerWidth ((Bank).chain.vertex k.succ.castSucc - (Bank).start)
      ((Bank).chain.edge k.castSucc) ((Bank).chain.edge k.succ) =
        C.totalAngle Retain (C.boundaryEndVertex Retain ((Chain).point k.succ)) := by
  let w := C.boundaryEndVertex Retain ((Chain).point k.succ)
  have incoming : 0 < inner ℝ ((Bank).chain.vertex k.succ.castSucc - (Bank).start)
      ((Bank).chain.edge k.castSucc) := by
    have genuine : (Bank).chain.vertex k.castSucc.castSucc ≠ (Bank).chain.vertex k.castSucc.succ :=
      Ne.symm (sub_ne_zero.mp (C.boundaryChainRoll_edge_ne_zero Chain k.castSucc))
    simpa only [PolygonalChain.edge, Fin.succ_castSucc] using
      (Bank).inner_terminal_edge_pos outward k.castSucc genuine
  have original := R.contourSourceBankChain_original Q starts event k.succ
  have before : k.succ.val < R.parents.distanceToRoot Source := by
    rw [C.positiveContourBank_span R.selection Q event]
    exact k.succ.isLt
  have internal : ¬ C.IsBoundaryVertex Set.univ (C.vertexForgetCuts (Set.subset_univ Retain) w) := by
    intro boundary
    exact R.parents.iterate_lt_distanceToRoot_not_mem Source before
      (original ▸ R.boundary_roots boundary)
  have small : C.totalAngle Retain w ≤ 2 * π :=
    (C.totalAngle_le_forgetCuts (Set.subset_univ Retain) w).trans (K.totalAngle_le_two_pi _ internal)
  exact C.boundaryChainRoll_left_aperture Chain k _ incoming strict small

/-- The tip of the real saved gap retains its source defect as the aperture. -/
theorem contourSource_gap_tip_chart (G : OrientedBankGap Bank Opened) :
    let d := (Bank).chain.edge 0
    let x := G.model.edgePoint false 0 0
    0 < ‖d‖ ∧ ∃ chart : Metric.eball x (ENNReal.ofReal ‖d‖) ≃ᵢ
      Metric.eball (closedAngularSectorOrigin event.property.2.le) (ENNReal.ofReal ‖d‖),
      ∀ (side : Bool) (t : unitInterval)
        (near : edist (G.model.edgePoint side 0 t) x < ENNReal.ofReal ‖d‖),
        (chart ⟨G.model.edgePoint side 0 t, near⟩).val.val =
          if side then (t.val * ‖d‖) • polarRay Defect else (t.val * ‖d‖ : ℝ) := by
  have internal : ¬ C.IsBoundaryVertex Set.univ Source := fun boundary =>
    C.positiveContourVertex_nonroot R.selection Q event (R.boundary_roots boundary)
  have small : Defect < 2 * π := by
    rw [TriangleComplex.interiorAngularDefect, ite_eq_right internal]
    exact sub_lt_self _ (C.totalAngle_pos Set.univ Source)
  exact OrientedBankGap.sourceRotation_angular_chart Bank event.property.2 small
    (C.boundaryChainRoll_edge_ne_zero Chain 0) G

/-- On a saved bank bend the two oriented gap corners have the actual retained fan
angle and its full-turn complement. -/
theorem contourSource_gap_bend_chart (G : OrientedBankGap Bank Opened)
    (k : Fin Length) (side : Bool)
    (strict : 0 < inner ℝ ((Bank).chain.vertex k.succ.castSucc - (Bank).start) ((Bank).chain.edge k.succ)) :
    let bank := G.model.bank side
    let p := bank.chain.vertex k.succ.castSucc
    let incoming := bank.chain.edge k.castSucc
    let outgoing := bank.chain.edge k.succ
    let saved := C.totalAngle Retain (C.boundaryEndVertex Retain ((Chain).point k.succ))
    let θ := if side then 2 * π - saved else saved
    let frame := if side then radialRightCornerFrame (p - bank.start) incoming
      else radialLeftCornerFrame (p - bank.start) outgoing
    let x := G.model.edgePoint side k.succ 0
    ∃ (pos : 0 < θ) (r : ℝ), 0 < r ∧
      ∃ A : Metric.eball x (ENNReal.ofReal r) ≃ᵢ
          Metric.eball (closedAngularSectorOrigin pos.le) (ENNReal.ofReal r),
        ∀ y, p + frame (A y).val.val = y.val.val := by
  let bank := G.model.bank side
  let p := bank.chain.vertex k.succ.castSucc
  let frame := if side then radialRightCornerFrame (p - bank.start) (bank.chain.edge k.castSucc)
    else radialLeftCornerFrame (p - bank.start) (bank.chain.edge k.succ)
  let saved := C.totalAngle Retain (C.boundaryEndVertex Retain ((Chain).point k.succ))
  let θ := if side then 2 * Real.pi - saved else saved
  let width := if side then
    radialRightCornerWidth (p - bank.start)
      (bank.chain.edge k.castSucc) (bank.chain.edge k.succ)
    else radialLeftCornerWidth (p - bank.start)
      (bank.chain.edge k.castSucc) (bank.chain.edge k.succ)
  have nonzero (i : Fin (Length + 1)) : bank.chain.edge i ≠ 0 := by
    have genuine : (Bank).chain.edge i ≠ 0 := C.boundaryChainRoll_edge_ne_zero Chain i
    cases side
    · exact genuine
    · change ((Bank).rotateSuffix 0 Defect).chain.edge i ≠ 0
      rw [(Bank).rotateSuffix_zero_edge]
      simpa only [map_zero] using (complexRotation Defect).injective.ne genuine
  have radial : 0 < inner ℝ (p - bank.start) (bank.chain.edge k.succ) := by
    cases side
    · exact strict
    · change 0 < inner ℝ (((Bank).rotateSuffix 0 Defect).chain.vertex k.succ.castSucc -
        ((Bank).rotateSuffix 0 Defect).start) (((Bank).rotateSuffix 0 Defect).chain.edge k.succ)
      rw [(Bank).rotateSuffix_zero_vertex_sub_start, (Bank).rotateSuffix_zero_edge,
        LinearIsometry.inner_map_map]
      exact strict
  have first := R.contourSource_first_bend_aperture Q starts event k G.first_outward strict
  have same : width = θ := by
    cases side
    · exact first
    · let Q := (Bank).rotateSuffix 0 Defect
      let right := radialRightCornerWidth (Q.chain.vertex k.succ.castSucc - Q.start)
        (Q.chain.edge k.castSucc) (Q.chain.edge k.succ)
      have balance : saved + right = 2 * Real.pi :=
        (congrArg (fun a => a + right) first.symm).trans
          (PolygonalRay.sourceOpening_corner_widths_add (B := Bank) Defect k)
      change right = 2 * Real.pi - saved
      linarith only [balance]
  obtain ⟨pos, small, r, rpos, A, _, physical⟩ := G.exists_model_bend_chart side k nonzero radial
  have θpos : 0 < θ := same ▸ pos
  let F := bisectedSectorFan width pos small
  have angle : F.totalAngle = θ := (bisectedSectorFan_totalAngle width pos small).trans same
  let E := (F.intrinsicAngularSectorIsometryEquiv (angle.trans_lt (same ▸ small))).trans
    (PolygonalPoint.congrIsometryEquiv (congrArg closedAngularSector angle))
  have center : E F.origin = closedAngularSectorOrigin θpos.le := by
    apply PolygonalPoint.ext
    rw [IsometryEquiv.trans_apply, PolygonalPoint.congrIsometryEquiv_val,
      AngularFan.intrinsicAngularSectorIsometryEquiv_val, AngularFan.develop_origin]
    rfl
  refine ⟨θpos, r, rpos, A.trans (basedEBallIsometry E F.origin _ center (ENNReal.ofReal r)), ?_⟩
  intro y
  change p + frame (E (A y).val).val = _
  rw [IsometryEquiv.trans_apply, PolygonalPoint.congrIsometryEquiv_val,
    AngularFan.intrinsicAngularSectorIsometryEquiv_val]
  exact physical y

end Unfoldings.ConvexRoof.PotentialCutForest
