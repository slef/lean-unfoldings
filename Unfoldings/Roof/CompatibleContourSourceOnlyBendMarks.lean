module

public import Unfoldings.Geometry.OrientedBankGapBendParameters
public import Unfoldings.Roof.CompatibleContourSourceOnlyBendChart
public import Unfoldings.Roof.CompatibleContourSourceOnlyChildFans
public import Unfoldings.Roof.CompatibleContourSourceOnlyGapVertexMarks

/-! Calibrated bend charts with original incoming and outgoing physical parameters. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)
  (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
  (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)
  (beta : 0 ≤ β) (acute : β < Real.pi / 2)

local notation "T" => K.compatibleCutMesh compact nonempty R no_boundary level higher M
  positive inner_disk
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance sourceOnlyBendMarkIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
variable (contour :
    (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.BoundaryContour
    ((K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.selectedRetain
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection))
  (starts : (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.contourOriginalVertex
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour 0 ∈
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).parents.roots)

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
variable (geometry : ∀ event :
    (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    OrientedBankGap
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local notation "models" => (fun event : Event => OrientedBankGap.model (geometry event))
local notation "Gap" => K.compatibleContourSourceOnlyGapMark compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts models

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "FiniteBank[" v "," h "]" => (Sum.inl (Subtype.mk v h) : Attachment)
local notation "BankAt[" e "]" => K.compatibleContourSourceBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "MovedAt[" e "]" => K.compatibleContourSourceOnlyBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e

local notation "IndexAt[" v "," h "," e "," member "]" =>
  TriangleComplex.contourGapBankIndex D Selection contour v h e
    (Iff.mpr (TriangleComplex.mem_contourEdgeGapStack D Selection contour v e)
      (Iff.mp (TriangleComplex.mem_contourSavedGapStack D Selection contour v e) member))
local notation "BankLength[" v "," h "]" => TriangleComplex.boundaryBankLength D
  (TriangleComplex.contourParentBank D Selection contour (PotentialCutForest.boundary_roots Fcut)
    starts v h false)
local notation "LengthAt[" e "]" => TriangleComplex.positiveContourBankLength D Selection contour e
local notation "AngleAt[" e "," i "]" => K.compatibleContourSourceBankFanAngle compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts e i

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
    (D).contourGapBankIndex_parent Selection contour v nonroot parent_nonroot e _ _
  let k : Fin LengthAt[e] := ⟨i.val, by have bound := j.isLt; omega⟩
  exact ⟨k, Fin.ext rfl, Fin.ext next.symm⟩

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
  have distance := K.compatibleContourSourceOnlyEdgeMetric compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts models v nonroot
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

omit beta acute in
private theorem time_to_start (t : unitInterval) : edist t 0 = ENNReal.ofReal t.val := by
  rw [edist_dist]
  change ENNReal.ofReal (dist t.val 0) = _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]

omit beta acute in
private theorem time_to_finish (t : unitInterval) :
    edist (unitInterval.symm t) 1 = ENNReal.ofReal t.val := by
  rw [edist_dist]
  change ENNReal.ofReal (dist (1 - t.val) 1) = _
  rw [Real.dist_eq, sub_right_comm, sub_self, zero_sub, abs_neg, abs_of_nonneg t.property.1]

/-- The distances to the bend keep the literal original edge speeds. Incoming
time is measured backwards from the bend. -/
theorem compatibleContourSourceOnlyGap_parent_bend_distance
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
  have metric_out := K.compatibleContourSourceOnlyEdgeMetric compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts models parent parent_nonroot
    e above side t 0
  have metric_in := K.compatibleContourSourceOnlyEdgeMetric compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts models v nonroot e here side
    (unitInterval.symm t) 1
  have join : Gap FiniteBank[v,nonroot] e here side 1 = center :=
    K.compatibleContourSourceOnlyGapMark_parent_join compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts models v nonroot parent_nonroot e here above side
  have scale (l : ℝ) (d : ℝ≥0∞) (same : d = ENNReal.ofReal t.val) :
      ENNReal.ofReal l * d = ENNReal.ofReal (t.val * l) :=
    (congrArg (ENNReal.ofReal l * ·) same).trans
      ((mul_comm _ _).trans (ENNReal.ofReal_mul t.property.1).symm)
  cases ray
  · exact metric_out.trans (scale _ _ (time_to_start t))
  · exact (congrArg (edist (Gap FiniteBank[v,nonroot] e here side (unitInterval.symm t)))
      join.symm).trans (metric_in.trans (scale _ _ (time_to_finish t)))

set_option maxHeartbeats 220000 in
-- Exact edge names require transporting both dependent parameters through their Fin indices.
/-- Each original parent bend chart retains the saved aperture and both literal bank rays. -/
theorem compatibleContourSourceOnlyGap_parent_bend_marked_chart
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
  let G := geometry e
  let B := (models e).bank flag
  obtain ⟨k, kin, kout⟩ := exists_parent_bend_indices K compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour v nonroot parent_nonroot e here above
  have hi : k.castSucc = i := kin
  have hj : k.succ = j := kout
  let d := B.chain.vertex k.succ.castSucc - B.start
  let width := cond flag (radialRightCornerWidth d (B.chain.edge k.castSucc) (B.chain.edge k.succ))
    (radialLeftCornerWidth d (B.chain.edge k.castSucc) (B.chain.edge k.succ))
  have genuine := K.compatibleContourSourceOnlyBank_edge_ne_zero compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts models e flag
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
    let κ := (D).interiorAngularDefect Set.univ ((D).positiveContourVertex Selection contour e)
    have left := K.compatibleContourSourceBank_first_bend_aperture compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts e k G.first_outward (strict k)
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
    G.exists_model_bend_marked_chart flag k genuine radial
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
    have left := gap_edge_speed K compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts geometry v nonroot e here side
    have right := gap_edge_speed K compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts geometry parent parent_nonroot e above side
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

end Unfoldings.ConvexRoof
