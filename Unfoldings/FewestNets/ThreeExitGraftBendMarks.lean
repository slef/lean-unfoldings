module

public import Unfoldings.FewestNets.ThreeExitGraftMarkMetrics
public import Unfoldings.Roof.PotentialContourFanAngles
public import Unfoldings.Roof.PotentialContourGapVertexMarks
public import Unfoldings.Roof.PotentialContourGapSectors
public import Unfoldings.Geometry.OrientedBankGapBendParameters
public import Unfoldings.Cone.MarkedSectorGerm



/-! Whole marked sector charts at actual finite gap bends. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel

open MetricGluing

universe u v

set_option maxHeartbeats 1800000

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : FewestNets.ThreeExitStemWindows}
  {R : K.ThreeExitComponentRouting seed B compact nonempty H}

local notation "U" => K.selectionComponent slopes seed
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ K.restrictedCarrier U}
local notation "G" => SlopeEnvelope.recenter
  (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty) B.reference
local notation "pointOf" => (fun v : V => K.projectedVertex (Subtype.val v))

variable {level : ℝ}
  {M : (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel}
  (L : R.FloorWindowModel level M)

local notation "T[" h "]" => R.fineMesh level M h
local notation "D[" h "]" => SpatialEnvelope.FloorMesh.pairedComplex T[h]
local notation "F[" h "]" => R.fineMeshForest level M h
local notation "Sel[" h "]" => PotentialCutForest.selection F[h]

local instance graftBendMarksIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
    Fintype (T[h]).Index := @Fintype.ofFinite _ (T[h]).finite

variable (S : SourceContour (R := R) (M := M) (level := level))

local notation "T" => T[S.higher]
local notation "D" => D[S.higher]
local notation "Fcut" => F[S.higher]
local notation "Selection" => Sel[S.higher]
local notation "Event" => TriangleComplex.PositiveContourSource D Selection S.contour
local notation "Model[" e "]" => OrientedBankGap.model (S.gaps e)
local notation "Pieces" => polygonalBankStackPiece L.whole.Cut (fun e : Event => BankGapModel.region (Model[e]))
local notation "Stack" => PotentialCutForest.contourAttachmentStack Fcut S.contour
local notation "Base" => contourBaseMark L S
local notation "Gap" => PotentialCutForest.contourGapMark Fcut S.contour S.starts
  (fun e : Event => Model[e])
local notation "Attachment" => PotentialCutForest.ContourAttachment Fcut
local notation "Param" => PotentialCutForest.contourAttachmentParameter Fcut

local notation "Child" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "FiniteBank[" v "," h "]" => (Sum.inl (Subtype.mk v h) : Attachment)
local notation "BankAt[" e "]" => PotentialCutForest.contourSourceRay Fcut S.contour S.starts e
local notation "models" => (fun e : Event => Model[e])
local notation "geometry" => S.gaps
local notation "IndexAt[" v "," h "," e "," member "]" =>
  TriangleComplex.contourGapBankIndex D Selection S.contour v h e
    (Iff.mpr (TriangleComplex.mem_contourEdgeGapStack D Selection S.contour v e)
      (Iff.mp (TriangleComplex.mem_contourSavedGapStack D Selection S.contour v e) member))
local notation "BankLength[" v "," h "]" => TriangleComplex.boundaryBankLength D
  (TriangleComplex.contourParentBank D Selection S.contour (PotentialCutForest.boundary_roots Fcut)
    S.starts v h false)
local notation "LengthAt[" e "]" => TriangleComplex.positiveContourBankLength D Selection S.contour e
local notation "AngleAt[" e "," i "]" => PotentialCutForest.contourSourceBankFanAngle Fcut S.contour S.starts e i

include L in
/-- The original interval has the intrinsic length of its unrefined parent bank. -/
theorem edist_contourGapMark_eq_length
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots)
    (e : Event) (member : e ∈ Stack FiniteBank[v,nonroot]) (side : Bool) (s t : unitInterval) :
    edist (Gap FiniteBank[v,nonroot] e member side s) (Gap FiniteBank[v,nonroot] e member side t) =
      ENNReal.ofReal BankLength[v,nonroot] * edist s t := by
  let bank := (D).contourParentBank Selection S.contour (Fcut).boundary_roots
    S.starts v nonroot false
  let : MetricSpace (Param FiniteBank[v,nonroot]) :=
    contourAttachmentMetric S FiniteBank[v,nonroot]
  have first := L.edist_contourGapMark_eq_base S FiniteBank[v,nonroot] e member side s t
  exact first.trans ((L.fineMeshWholeMap_edist_bank S.higher bank s t).trans
    ((T).pairedFolding.edist_directedBoundaryPath_eq_length bank s t))

private theorem exists_parent_bend_indices
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots)
    (parent_nonroot : (Fcut).parents.parent v ∉ (Fcut).parents.roots)
    (e : Event) (here : e ∈ Stack FiniteBank[v,nonroot])
    (above : e ∈ Stack FiniteBank[(Fcut).parents.parent v,parent_nonroot]) :
    ∃ k : Fin LengthAt[e], k.castSucc = IndexAt[v,nonroot,e,here] ∧
      k.succ = IndexAt[(Fcut).parents.parent v,parent_nonroot,e,above] := by
  let p := (Fcut).parents.parent v
  let i := IndexAt[v,nonroot,e,here]
  let j := IndexAt[p,parent_nonroot,e,above]
  have next : j.val = i.val + 1 :=
    (D).contourGapBankIndex_parent Selection S.contour v nonroot parent_nonroot e _ _
  let k : Fin LengthAt[e] := ⟨i.val, by have bound := j.isLt; omega⟩
  exact ⟨k, Fin.ext rfl, Fin.ext next.symm⟩

include L in
private theorem gap_edge_speed
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots)
    (e : Event) (member : e ∈ Stack FiniteBank[v,nonroot]) (side : Bool) :
    ‖((models e).bank (!side)).chain.edge IndexAt[v,nonroot,e,member]‖ = BankLength[v,nonroot] := by
  let i := IndexAt[v,nonroot,e,member]
  let norm := ‖((models e).bank (!side)).chain.edge i‖
  let ell := BankLength[v,nonroot]
  have one : edist (0 : unitInterval) 1 = 1 := by
    rw [edist_dist]
    change ENNReal.ofReal (dist (0 : ℝ) 1) = 1
    norm_num
  have distance := L.edist_contourGapMark_eq_length S v nonroot
    e member side 0 1
  have measured : edist (Gap FiniteBank[v,nonroot] e member side 0)
      (Gap FiniteBank[v,nonroot] e member side 1) = ENNReal.ofReal norm * edist (0 : unitInterval) 1 :=
    ((models e).edist_edgePoint (!side) i 0 1).trans
      (by
      dsimp only [norm]
      rw [ofReal_norm, enorm_eq_nnnorm])
  have eq : ENNReal.ofReal norm * edist (0 : unitInterval) 1 =
      ENNReal.ofReal ell * edist (0 : unitInterval) 1 := measured.symm.trans distance
  rw [one, mul_one, mul_one] at eq
  exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) ((D).boundaryBankLength_pos _).le).mp eq

private theorem time_to_start (t : unitInterval) : edist t 0 = ENNReal.ofReal t.val := by
  rw [edist_dist]
  change ENNReal.ofReal (dist t.val 0) = _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]

private theorem time_to_finish (t : unitInterval) :
    edist (unitInterval.symm t) 1 = ENNReal.ofReal t.val := by
  rw [edist_dist]
  change ENNReal.ofReal (dist (1 - t.val) 1) = _
  rw [Real.dist_eq, sub_right_comm, sub_self, zero_sub, abs_neg, abs_of_nonneg t.property.1]

include L in
/-- The distances to the bend keep the literal original edge speeds. Incoming
time is measured backwards from the bend. -/
theorem contourGraftGap_parent_bend_distance
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots)
    (parent_nonroot : (Fcut).parents.parent v ∉ (Fcut).parents.roots)
    (e : Event) (here : e ∈ Stack FiniteBank[v,nonroot])
    (above : e ∈ Stack FiniteBank[(Fcut).parents.parent v,parent_nonroot])
    (side ray : Bool) (t : unitInterval) :
    let parent := (Fcut).parents.parent v
    let center := Gap FiniteBank[parent,parent_nonroot] e above side 0
    let mark := if ray then Gap FiniteBank[v,nonroot] e here side (unitInterval.symm t)
      else Gap FiniteBank[parent,parent_nonroot] e above side t
    let length := if ray then BankLength[v,nonroot] else BankLength[parent,parent_nonroot]
    edist mark center = ENNReal.ofReal (t.val * length) := by
  let parent := (Fcut).parents.parent v
  let center := Gap FiniteBank[parent,parent_nonroot] e above side 0
  have metric_out := L.edist_contourGapMark_eq_length S parent parent_nonroot
    e above side t 0
  have metric_in := L.edist_contourGapMark_eq_length S v nonroot e here side
    (unitInterval.symm t) 1
  have join : Gap FiniteBank[v,nonroot] e here side 1 = center :=
    (Fcut).contourGapMark_parent_join S.contour S.starts S.gaps v nonroot parent_nonroot e here above side
  have scale (l : ℝ) (d : ℝ≥0∞) (same : d = ENNReal.ofReal t.val) :
      ENNReal.ofReal l * d = ENNReal.ofReal (t.val * l) :=
    (congrArg (ENNReal.ofReal l * ·) same).trans
      ((mul_comm _ _).trans (ENNReal.ofReal_mul t.property.1).symm)
  cases ray
  · exact metric_out.trans (scale _ _ (time_to_start t))
  · exact (congrArg (edist (Gap FiniteBank[v,nonroot] e here side (unitInterval.symm t)))
      join.symm).trans (metric_in.trans (scale _ _ (time_to_finish t)))

include L in
set_option maxHeartbeats 2900000 in
-- Exact edge names require transporting both dependent parameters through their Fin indices.
/-- Each original parent bend chart retains the saved aperture and both literal bank rays. -/
theorem contourGraftGap_parent_bend_marked_chart
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots)
    (parent_nonroot : (Fcut).parents.parent v ∉ (Fcut).parents.roots)
    (e : Event) (here : e ∈ Stack FiniteBank[v,nonroot])
    (above : e ∈ Stack FiniteBank[(Fcut).parents.parent v,parent_nonroot])
    (strict : ∀ k : Fin LengthAt[e], let B := BankAt[e]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ))
    (side : Bool) :
    let parent := (Fcut).parents.parent v
    let center := Gap FiniteBank[parent,parent_nonroot] e above side 0
    let mark (ray : Bool) (t : unitInterval) :=
      if ray then Gap FiniteBank[v,nonroot] e here side (unitInterval.symm t)
      else Gap FiniteBank[parent,parent_nonroot] e above side t
    let length (ray : Bool) := if ray then BankLength[v,nonroot] else BankLength[parent,parent_nonroot]
    let saved := AngleAt[e,IndexAt[parent,parent_nonroot,e,above]]
    let θ := if side then saved else 2 * Real.pi - saved
    ∃ (pos : 0 < θ) (r : ℝ) (rpos : 0 < r)
      (A : Metric.eball center (ENNReal.ofReal r) ≃ᵢ
        Metric.eball (closedAngularSectorOrigin pos.le) (ENNReal.ofReal r)),
      (A ⟨center, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)⟩).val =
        closedAngularSectorOrigin pos.le ∧
      ∀ (ray : Bool) (t : unitInterval) (near : edist (mark ray t) center < ENNReal.ofReal r),
        (A ⟨mark ray t, near⟩).val.val =
          if ray = side then (t.val * length ray) • polarRay θ else (t.val * length ray : ℝ) := by
  let parent := (Fcut).parents.parent v
  let i := IndexAt[v,nonroot,e,here]
  let j := IndexAt[parent,parent_nonroot,e,above]
  let saved := AngleAt[e,j]
  let θ := if side then saved else 2 * Real.pi - saved
  let flag := !side
  let gap := geometry e
  let B := (models e).bank flag
  obtain ⟨k, kin, kout⟩ := exists_parent_bend_indices S v nonroot parent_nonroot e here above
  have hi : k.castSucc = i := kin
  have hj : k.succ = j := kout
  let d := B.chain.vertex k.succ.castSucc - B.start
  let width := cond flag (radialRightCornerWidth d (B.chain.edge k.castSucc) (B.chain.edge k.succ))
    (radialLeftCornerWidth d (B.chain.edge k.castSucc) (B.chain.edge k.succ))
  have genuine := (Fcut).contourGapBank_genuine S.contour S.starts S.gaps e flag
  have radial : 0 < inner ℝ d (B.chain.edge k.succ) := by
    have st := strict k
    cases side
    · let orig := BankAt[e]
      change 0 < inner ℝ ((orig.rotateSuffix 0 _).chain.vertex k.succ.castSucc -
        (orig.rotateSuffix 0 _).start) ((orig.rotateSuffix 0 _).chain.edge k.succ)
      rw [orig.rotateSuffix_zero_vertex_sub_start, orig.rotateSuffix_zero_edge,
        LinearIsometry.inner_map_map]
      exact st
    · exact st
  have width_saved : width = θ := by
    let orig := BankAt[e]
    let κ := (D).interiorAngularDefect Set.univ ((D).positiveContourVertex Selection S.contour e)
    have left := (Fcut).contourSource_first_bend_aperture S.contour S.starts e k gap.first_outward (strict k)
    have at_parent : AngleAt[e,k.succ] = saved := congrArg (fun l => AngleAt[e,l]) hj
    have left_saved : radialLeftCornerWidth (orig.chain.vertex k.succ.castSucc - orig.start)
        (orig.chain.edge k.castSucc) (orig.chain.edge k.succ) = saved := left.trans at_parent
    have full := PolygonalRay.sourceOpening_corner_widths_add (B := orig) κ k
    cases side
    · change radialRightCornerWidth _ _ _ = 2 * Real.pi - saved
      have balance : saved + radialRightCornerWidth d (B.chain.edge k.castSucc)
          (B.chain.edge k.succ) = 2 * Real.pi :=
        (congrArg (· + radialRightCornerWidth d (B.chain.edge k.castSucc) (B.chain.edge k.succ))
          left_saved.symm).trans full
      linarith only [balance]
    · exact left_saved
  obtain ⟨wpos, r, rpos, chart, cent, in_coord, out_coord⟩ :=
    gap.exists_model_bend_marked_chart flag k genuine radial
  let p := (models e).edgePoint flag k.succ 0
  let center := Gap FiniteBank[parent,parent_nonroot] e above side 0
  let mark (ray : Bool) (t : unitInterval) :=
    if ray then Gap FiniteBank[v,nonroot] e here side (unitInterval.symm t)
    else Gap FiniteBank[parent,parent_nonroot] e above side t
  let length (ray : Bool) := if ray then BankLength[v,nonroot] else BankLength[parent,parent_nonroot]
  have base : p = center := congrArg (fun l => (models e).edgePoint flag l 0) hj
  let Spec (w : ℝ) (z : PolygonalPoint (models e).region) : Prop :=
    ∃ (pos : 0 < w) (r : ℝ) (rpos : 0 < r)
      (A : Metric.eball z (ENNReal.ofReal r) ≃ᵢ
        Metric.eball (closedAngularSectorOrigin pos.le) (ENNReal.ofReal r)),
      (A ⟨z, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)⟩).val =
        closedAngularSectorOrigin pos.le ∧
      ∀ (ray : Bool) (t : unitInterval) (near : edist (mark ray t) z < ENNReal.ofReal r),
        (A ⟨mark ray t, near⟩).val.val =
          if ray = side then (t.val * length ray) • polarRay w else (t.val * length ray : ℝ)
  have at_width : Spec width p := by
    have left := gap_edge_speed L S v nonroot e here side
    have right := gap_edge_speed L S parent parent_nonroot e above side
    have incoming : ‖B.chain.edge k.castSucc‖ = BankLength[v,nonroot] :=
      (congrArg (fun l => ‖B.chain.edge l‖) hi).trans left
    have outgoing : ‖B.chain.edge k.succ‖ = BankLength[parent,parent_nonroot] :=
      (congrArg (fun l => ‖B.chain.edge l‖) hj).trans right
    refine ⟨wpos, r, rpos, chart, cent, ?_⟩
    intro ray t near
    cases ray
    · have same : mark false t = (models e).edgePoint flag k.succ t :=
        congrArg (fun l => (models e).edgePoint flag l t) hj.symm
      have close := (congrArg (edist · p) same).symm.trans_lt near
      have arg : (⟨mark false t, near⟩ : Metric.eball p (ENNReal.ofReal r)) =
          ⟨(models e).edgePoint flag k.succ t, close⟩ := Subtype.ext same
      have eq := (congrArg (fun x => (chart x).val.val) arg).trans (out_coord t close)
      have speed_eq := congrArg (fun l : ℝ =>
        if flag then (t.val * l) • polarRay width else ((t.val * l : ℝ) : ℂ)) outgoing
      exact eq.trans (speed_eq.trans (by cases side <;> rfl))
    · have same : mark true t = (models e).edgePoint flag k.castSucc (unitInterval.symm t) :=
        congrArg (fun l => (models e).edgePoint flag l (unitInterval.symm t)) hi.symm
      have close := (congrArg (edist · p) same).symm.trans_lt near
      have arg : (⟨mark true t, near⟩ : Metric.eball p (ENNReal.ofReal r)) =
          ⟨(models e).edgePoint flag k.castSucc (unitInterval.symm t), close⟩ := Subtype.ext same
      have eq := (congrArg (fun x => (chart x).val.val) arg).trans
        (in_coord (unitInterval.symm t) close)
      have rt : 1 - (unitInterval.symm t).val = t.val := by
        change 1 - (1 - t.val) = t.val
        ring
      have speed_eq := congrArg₂ (fun s l : ℝ =>
        if flag then ((s * l : ℝ) : ℂ) else (s * l) • polarRay width) rt incoming
      exact eq.trans (speed_eq.trans (by cases side <;> rfl))
  have normalized : Spec θ p := Eq.mp (congrArg (Spec · p) width_saved) at_width
  exact Eq.mp (congrArg (Spec θ) base) normalized

include L in
/-- The actual gap bend, with the appropriate original incoming or outgoing bank
as its initial ray and the other as its terminal ray. -/
theorem contourGraftGapBend_markedSectorGerm
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots)
    (parent_nonroot : (Fcut).parents.parent v ∉ (Fcut).parents.roots)
    (e : Event) (here : e ∈ Stack FiniteBank[v,nonroot])
    (above : e ∈ Stack FiniteBank[(Fcut).parents.parent v,parent_nonroot])
    (strict : ∀ k : Fin LengthAt[e], let B := BankAt[e]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ))
    (side : Bool) :
    let parent := (Fcut).parents.parent v
    let center := Gap FiniteBank[parent,parent_nonroot] e above side 0
    let bank (ray : Bool) (t : unitInterval) :=
      if ray then Gap FiniteBank[v,nonroot] e here side (unitInterval.symm t)
      else Gap FiniteBank[parent,parent_nonroot] e above side t
    let speed (ray : Bool) := if ray then BankLength[v,nonroot] else BankLength[parent,parent_nonroot]
    let saved := AngleAt[e,IndexAt[parent,parent_nonroot,e,above]]
    let θ := if side then saved else 2 * Real.pi - saved
    let ray (b : Bool) := if b then side else !side
    Nonempty (MarkedSectorGerm center θ (fun b => bank (ray b)) (fun b => speed (ray b))) := by
  dsimp only
  obtain ⟨positive_angle, r, positive_radius, chart, center, coords⟩ :=
    L.contourGraftGap_parent_bend_marked_chart S
      v nonroot parent_nonroot e here above strict side
  refine ⟨⟨⟨positive_angle, r, positive_radius, chart, center⟩, ?_, ?_⟩⟩
  · intro b t
    exact L.contourGraftGap_parent_bend_distance S
      v nonroot parent_nonroot e here above side (if b then side else !side) t
  · intro b t near
    have h := coords (if b then side else !side) t near
    cases side <;> cases b <;>
      simpa only [Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false, ite_true, ite_false,
        polarRay_zero, Complex.real_smul, mul_one] using h

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
