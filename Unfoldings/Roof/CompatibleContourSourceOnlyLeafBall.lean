module

public import Unfoldings.Cone.MarkedSectorGerm
public import Unfoldings.Cone.SectorPairBankRays
public import Unfoldings.Cone.SectorPairConstruction
public import Unfoldings.Metric.BankStackSingleton
public import Unfoldings.Roof.CompatibleContourSourceOnlyLeafClasses
public import Unfoldings.Roof.CompatibleContourSourceOnlyLeafRoofChart
public import Unfoldings.Roof.CompatibleContourSourceOnlySourceChart

/-! The original roof and gap sectors meet along the two whole metric rays at a leaf. -/

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

local instance sourceOnlyLeafBallIndexFintype : Fintype (T).Index :=
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
  (W : R.WholeCutModel M)
  (models : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    BankGapModel
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance sourceOnlyLeafBallWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Pieces" => polygonalBankStackPiece W.Cut
  (fun event : Event => BankGapModel.region (models event))
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "Gap" => K.compatibleContourSourceOnlyGapMark compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts models

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "BankAt[" e "]" => K.compatibleContourSourceBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "MovedAt[" e "]" => K.compatibleContourSourceOnlyBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "SourceOf[" e "]" => TriangleComplex.positiveContourVertex D Selection contour e
local notation "FirstEdge[" e "]" => (Sum.inl
  (Subtype.mk SourceOf[e] (TriangleComplex.positiveContourVertex_nonroot D Selection contour e)) :
    Attachment)
local notation "RoofPoint[" e "]" => (Sigma.mk none (Base FirstEdge[e] false 0) :
  MetricGluing.Total Pieces)
local notation "GapPoint[" e "]" => (Sigma.mk (some e)
  (BankGapModel.edgePoint (models e) false 0 0) :
  MetricGluing.Total Pieces)
local notation "L" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Rgt" => MetricGluing.bankStackRight Pieces Stack Base Gap

local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W
local notation "VertexAt[" w "]" => TriangleComplex.vertexPoint D (PotentialCutForest.retain Fcut) w
local notation "Banks" => MetricGluing.bankSeams L Rgt
local notation "Parent[" v "," h "," side "]" => TriangleComplex.contourParentBank D Selection
  contour (PotentialCutForest.boundary_roots Fcut) starts v h side

private theorem exists_leaf_gap_marked_chart
    (event : Event) (g : OrientedBankGap BankAt[event] MovedAt[event])
    (matched : models event = g.model) (member : event ∈ Stack FirstEdge[event])
    {ell : ℝ} (ellpos : 0 < ell) (gap_speed : ‖(BankAt[event]).chain.edge 0‖ = ell) :
    let edge := FirstEdge[event]
    let κ := (D).interiorAngularDefect Set.univ SourceOf[event]
    let center := (models event).edgePoint false 0 0
    ∃ chart : Metric.eball center (ENNReal.ofReal ell) ≃ᵢ
        Metric.eball (closedAngularSectorOrigin event.property.2.le) (ENNReal.ofReal ell),
      (chart ⟨center, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr ellpos)⟩).val =
        closedAngularSectorOrigin event.property.2.le ∧
      (∀ side (t : unitInterval),
        edist (Gap edge event member side t) center = ENNReal.ofReal (t.val * ell)) ∧
      ∀ (side : Bool) (t : unitInterval)
        (near : edist (Gap edge event member side t) center < ENNReal.ofReal ell),
        (chart ⟨Gap edge event member side t, near⟩).val.val =
          if side then ((t.val * ell : ℝ) : ℂ) else (t.val * ell) • polarRay κ := by
  let edge := FirstEdge[event]
  let κ := (D).interiorAngularDefect Set.univ SourceOf[event]
  have κpos : 0 < κ := event.property.2
  let Z := PolygonalPoint (models event).region
  let center : Z := (models event).edgePoint false 0 0
  let direct (b : Bool) (t : unitInterval) : Z := (models event).edgePoint b 0 t
  let modelChart (model : BankGapModel BankAt[event] MovedAt[event]) : Prop :=
    ∃ chart : Metric.eball (model.edgePoint false 0 0) (ENNReal.ofReal ell) ≃ᵢ
        Metric.eball (closedAngularSectorOrigin κpos.le) (ENNReal.ofReal ell),
      ∀ (b : Bool) (t : unitInterval)
        (near : edist (model.edgePoint b 0 t) (model.edgePoint false 0 0) < ENNReal.ofReal ell),
        (chart ⟨model.edgePoint b 0 t, near⟩).val.val =
          if b then (t.val * ell) • polarRay κ else (t.val * ell : ℝ)
  have available : modelChart g.model := by
    have same := K.compatibleContourSourceOnlyGap_source_angular_chart compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts event g
    dsimp only at same
    rw [gap_speed] at same
    exact same.2
  have raw : modelChart (models event) := matched.symm ▸ available
  obtain ⟨chart, ray⟩ := raw
  have gap_ray (side : Bool) (t : unitInterval)
      (near : edist (Gap edge event member side t) center < ENNReal.ofReal ell) :
      (chart ⟨Gap edge event member side t, near⟩).val.val =
        if side then ((t.val * ell : ℝ) : ℂ) else (t.val * ell) • polarRay κ := by
    have address : Gap edge event member side t = direct (!side) t :=
      K.compatibleContourSourceOnlyGapMark_source_edge compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts models event member side t
    have radial : edist (direct (!side) t) center < ENNReal.ofReal ell :=
      (congrArg (edist · center) address).symm.trans_lt near
    have argument : (⟨Gap edge event member side t, near⟩ :
        Metric.eball center (ENNReal.ofReal ell)) = ⟨direct (!side) t, radial⟩ :=
      Subtype.ext address
    have coords := (congrArg (fun z => (chart z).val.val) argument).trans (ray (!side) t radial)
    cases side
    · exact coords
    · exact coords
  have gap_end (side : Bool) :
      Gap edge event member side 0 = center :=
    K.compatibleContourSourceOnlyGapMark_at_source compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts models event g member side
  have gap_center :
      (chart ⟨center, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr ellpos)⟩).val =
        closedAngularSectorOrigin κpos.le := by
    apply PolygonalPoint.ext
    let u : Metric.eball center (ENNReal.ofReal ell) :=
      ⟨Gap edge event member true 0, (congrArg (edist · center) (gap_end true)).trans_lt
        (Metric.mem_eball_self (ENNReal.ofReal_pos.mpr ellpos))⟩
    have same : u = ⟨center, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr ellpos)⟩ :=
      Subtype.ext (gap_end true)
    exact (congrArg (fun y => (chart y).val.val) same).symm.trans
      ((gap_ray true 0 u.property).trans (by simp [closedAngularSectorOrigin]))
  have time_dist (t : unitInterval) : edist t (0 : unitInterval) = ENNReal.ofReal t.val := by
    rw [edist_dist]
    apply congrArg ENNReal.ofReal
    change dist t.val 0 = t.val
    rw [Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]
  have distance_gap (side : Bool) (t : unitInterval) :
      edist (Gap edge event member side t) center = ENNReal.ofReal (t.val * ell) := by
    have address (s : unitInterval) :
        Gap edge event member side s = (models event).edgePoint (!side) 0 s :=
      K.compatibleContourSourceOnlyGapMark_source_edge compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts models event member side s
    have speed : ‖((models event).bank (!side)).chain.edge 0‖ = ell := by
      cases side
      · change ‖(MovedAt[event]).chain.edge 0‖ = ell
        exact (congrArg norm ((BankAt[event]).rotateSuffix_zero_edge κ 0)).trans
          (((complexRotation κ).norm_map _).trans gap_speed)
      · exact gap_speed
    calc
      _ = edist ((models event).edgePoint (!side) 0 t) ((models event).edgePoint (!side) 0 0) :=
        congrArg₂ edist (address t) ((gap_end side).symm.trans (address 0))
      _ = (‖((models event).bank (!side)).chain.edge 0‖₊ : ℝ≥0∞) * edist t (0 : unitInterval) :=
        (models event).edist_edgePoint (!side) 0 t 0
      _ = ENNReal.ofReal ell * edist t (0 : unitInterval) := by
        let d := ((models event).bank (!side)).chain.edge 0
        have coe_norm : ENNReal.ofReal ‖d‖ = (‖d‖₊ : ℝ≥0∞) := by
          rw [ofReal_norm, enorm_eq_nnnorm]
        have normalized : (‖d‖₊ : ℝ≥0∞) = ENNReal.ofReal ell :=
          coe_norm.symm.trans (congrArg ENNReal.ofReal speed)
        exact congrArg (· * edist t (0 : unitInterval)) normalized
      _ = _ := by rw [time_dist, mul_comm t.val ell, ENNReal.ofReal_mul ellpos.le]
  exact ⟨chart, gap_center, distance_gap, gap_ray⟩

set_option maxHeartbeats 340000 in
-- The constructor compares the elaborated whole-cut chart and the dependent gap chart.
/-- The actual source tip gives a calibrated sector even when the source has children. -/
theorem compatibleContourSourceOnlyTip_markedSectorGerm
    (event : Event) (g : OrientedBankGap BankAt[event] MovedAt[event])
    (matched : models event = g.model) (member : event ∈ Stack FirstEdge[event]) :
    let vertex := SourceOf[event]
    let nonroot := (D).positiveContourVertex_nonroot Selection contour event
    let ell := (D).boundaryBankLength Parent[vertex,nonroot,false]
    Nonempty (MarkedSectorGerm ((models event).edgePoint false 0 0)
      ((D).interiorAngularDefect Set.univ vertex)
      (fun side t => Gap FirstEdge[event] event member (!side) t) (fun _ => ell)) := by
  let v := SourceOf[event]
  let nonroot := (D).positiveContourVertex_nonroot Selection contour event
  let ell := (D).boundaryBankLength Parent[v,nonroot,false]
  have ellpos : 0 < ell := (D).boundaryBankLength_pos _
  have speed : ‖(BankAt[event]).chain.edge 0‖ = ell :=
    K.compatibleContourSourceBank_edge_length compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts event 0
  obtain ⟨chart, center, distance, ray⟩ := exists_leaf_gap_marked_chart K compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts models event g
    matched member ellpos speed
  change Nonempty (MarkedSectorGerm ((models event).edgePoint false 0 0)
    ((D).interiorAngularDefect Set.univ v)
    (fun side t => Gap FirstEdge[event] event member (!side) t) (fun _ => ell))
  refine ⟨⟨⟨event.property.2, ell, ellpos, chart, center⟩, fun b t => distance (!b) t, ?_⟩⟩
  intro b t near
  cases b
  · change (chart ⟨Gap FirstEdge[event] event member true t, near⟩).val.val =
      (t.val * ell) • polarRay 0
    simpa only [ite_true, polarRay_zero, Complex.real_smul, mul_one] using ray true t near
  · exact ray false t near

private theorem exists_leaf_sector_pair
    (geometry : ∀ event : Event, OrientedBankGap BankAt[event] MovedAt[event])
    (matched : ∀ event, models event = (geometry event).model)
    (event : Event)
    (childless : ∀ v ∉ (Fcut).parents.roots, (Fcut).parents.parent v ≠ SourceOf[event])
    (member : event ∈ Stack FirstEdge[event])
    {window : ℝ} (window_pos : 0 < window) :
    let edge := FirstEdge[event]
    let v := SourceOf[event]
    let nonroot := (D).positiveContourVertex_nonroot Selection contour event
    let w := (D).boundaryEndVertex (Fcut).retain Parent[v,nonroot,false]
    let θ := (D).totalAngle (Fcut).retain w
    let a : Bool → MetricGluing.Total Pieces
      | false => RoofPoint[event]
      | true => GapPoint[event]
    let mark (b : Bool) (side : Bool) (t : unitInterval) : Pieces (a b).1 :=
      match b with
      | false => Base edge side t
      | true => Gap edge event member side t
    ∃ (pos : 0 < θ) (small : θ < 2 * Real.pi) (ρ : ℝ) (ell : ℝ),
      ρ ≤ window ∧ ρ ≤ ell ∧
      ∃ A : MetricGluing.SectorPairChart Pieces a pos small ρ,
        (∀ (b side : Bool) (t : unitInterval),
          edist (mark b side t) (a b).2 = ENNReal.ofReal (t.val * ell)) ∧
        ∀ (b side : Bool) (t : unitInterval)
          (near : edist (mark b side t) (a b).2 < ENNReal.ofReal ρ),
          (A.chart b ⟨mark b side t, near⟩).val.val =
            MetricGluing.SectorPairChart.bankRay θ side (t.val * ell) := by
  let v := SourceOf[event]
  let nonroot := (D).positiveContourVertex_nonroot Selection contour event
  let edge := FirstEdge[event]
  let p (side : Bool) := Parent[v,nonroot,side]
  let w := (D).boundaryEndVertex (Fcut).retain (p false)
  let θ := (D).totalAngle (Fcut).retain w
  let κ := (D).interiorAngularDefect Set.univ v
  let ell := (D).boundaryBankLength (p false)
  let a : Bool → MetricGluing.Total Pieces
    | false => RoofPoint[event]
    | true => GapPoint[event]
  have ellpos : 0 < ell := (D).boundaryBankLength_pos (p false)
  have gap_speed : ‖(BankAt[event]).chain.edge 0‖ = ell :=
    K.compatibleContourSourceBank_edge_length compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts event 0
  obtain ⟨θpos, rRoof, roof_pos, roof, complement, roof_center, distance_roof, roof_ray⟩ :=
    K.compatibleContourSourceOnlyLeaf_roof_marked_chart compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W event childless
  have κpos : 0 < κ := event.property.2
  have θsmall : θ < 2 * Real.pi := by linarith
  let g := geometry event
  obtain ⟨gap, gap_center, distance_gap, gap_ray⟩ := exists_leaf_gap_marked_chart K
    compact nonempty R no_boundary level higher M positive inner_disk beta acute contour starts
    models event g (matched event) member ellpos gap_speed
  let U := rotation (Circle.exp θ)
  let ρ := min (min rRoof ell) window
  have ρpos : 0 < ρ := lt_min (lt_min roof_pos ellpos) window_pos
  have ρroof : ρ ≤ rRoof := (min_le_left _ _).trans (min_le_left _ _)
  have ρgap : ρ ≤ ell := (min_le_left _ _).trans (min_le_right _ _)
  have different : (a false).1 ≠ (a true).1 := by
    intro h
    cases h
  let A := MetricGluing.SectorPairChart.fromSectors a θpos θsmall κpos complement
    roof_pos ellpos ρpos ρroof ρgap roof gap roof_center gap_center different
  let ray := MetricGluing.SectorPairChart.bankRay θ
  have gap_ray' (side : Bool) (t : unitInterval)
      (near : edist (Gap edge event member side t) (a true).2 < ENNReal.ofReal ρ) :
      (A.chart true ⟨Gap edge event member side t, near⟩).val.val = ray side (t.val * ell) := by
    have near' := near.trans_le (ENNReal.ofReal_le_ofReal ρgap)
    change U (gap ⟨Gap edge event member side t, near'⟩).val.val = _
    have place := congrArg U (gap_ray side t near')
    apply place.trans
    cases side
    · change polarRay θ * ((t.val * ell) • polarRay κ) = ((t.val * ell : ℝ) : ℂ)
      rw [Complex.real_smul, mul_left_comm, ← polarRay_add, complement]
      simp [polarRay]
    · change polarRay θ * (t.val * ell : ℝ) = (t.val * ell : ℝ) * polarRay θ
      exact mul_comm _ _
  let on_mark (b : Bool) (side : Bool) (t : unitInterval) : Pieces (a b).1 :=
    match b with
    | false => Base edge side t
    | true => Gap edge event member side t
  have distance (b side : Bool) (t : unitInterval) :
      edist (on_mark b side t) (a b).2 = ENNReal.ofReal (t.val * ell) := by
    cases b
    · exact distance_roof side t
    · exact distance_gap side t
  have coordinates (b side : Bool) (t : unitInterval)
      (near : edist (on_mark b side t) (a b).2 < ENNReal.ofReal ρ) :
      (A.chart b ⟨on_mark b side t, near⟩).val.val = ray side (t.val * ell) := by
    cases b
    · exact roof_ray side t (near.trans_le (ENNReal.ofReal_le_ofReal ρroof))
    · exact gap_ray' side t near
  exact ⟨θpos, θsmall, ρ, ell, min_le_right _ _, ρgap, A, distance, coordinates⟩

set_option maxHeartbeats 250000 in
-- Coverage and the named seam slots live in the full dependent graft.
/-- At a childless positive source, the original full graft has a whole planar ball. -/
theorem compatibleContourSourceOnlyLeaf_hasMetricBallChart
    (geometry : ∀ event : Event, OrientedBankGap BankAt[event] MovedAt[event])
    (matched : ∀ event, models event = (geometry event).model)
    (event : Event)
    (childless : ∀ v ∉ (Fcut).parents.roots, (Fcut).parents.parent v ≠ SourceOf[event]) :
    HasMetricBallChart ℂ (MetricGluing.point Pieces Banks RoofPoint[event]) := by
  let v := SourceOf[event]
  let nonroot := (D).positiveContourVertex_nonroot Selection contour event
  let edge := FirstEdge[event]
  let w := (D).boundaryEndVertex (Fcut).retain Parent[v,nonroot,false]
  let θ := (D).totalAngle (Fcut).retain w
  let a : Bool → MetricGluing.Total Pieces
    | false => RoofPoint[event]
    | true => GapPoint[event]
  have invariant : Stack edge = [event] :=
    (K.compatibleContourSourceOnlyLeaf_roof_fan compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W event nonroot childless).1
  have member : event ∈ Stack edge := by rw [invariant]; exact List.mem_cons_self
  let g := geometry event
  obtain ⟨rCover, cover_pos, cover⟩ := K.compatibleContourSourceOnlyGraft_piece_ball_cover
    compact nonempty R no_boundary level higher M positive inner_disk beta acute contour starts
    W models geometry (a false)
  obtain ⟨rSlots, slots_pos, slots⟩ := K.compatibleContourSourceOnlyLeaf_near_attachment compact
    nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W
    models geometry event childless
  let window := min rCover rSlots
  have window_pos : 0 < window := lt_min cover_pos slots_pos
  obtain ⟨pos, small, ρ, ell, app, ρgap, A, distance, coordinates⟩ :=
    exists_leaf_sector_pair K compact nonempty R no_boundary level higher M positive inner_disk
      beta acute contour starts W models geometry matched event childless member window_pos
  have ρcover : ρ ≤ rCover := app.trans (min_le_left _ _)
  have ρslots : ρ ≤ rSlots := app.trans (min_le_right _ _)
  let ray := MetricGluing.SectorPairChart.bankRay θ
  let on_mark (b : Bool) (side : Bool) (t : unitInterval) : Pieces (a b).1 :=
    match b with
    | false => Base edge side t
    | true => Gap edge event member side t
  have members := K.compatibleContourSourceOnlyLeaf_eqvGen_pair compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models event g childless
  have near_tags (r : ℝ) (small : r ≤ ρ) (b : MetricGluing.Total Pieces)
      (near : edist (MetricGluing.point Pieces Banks b)
        (MetricGluing.point Pieces Banks (a false)) < ENNReal.ofReal r) :
      ∃ (side : Bool) (x : Metric.eball (a side).2 (ENNReal.ofReal ρ)),
        MetricGluing.SectorPairChart.pairTag a side x = b ∧
          edist x.val (a side).2 < ENNReal.ofReal r := by
    have rpos : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le near)
    obtain ⟨c, relation, close⟩ := cover r rpos (small.trans ρcover) b
      ((edist_comm _ _).trans_lt near)
    have choose_side : ∃ side, (⟨b.1, c⟩ : MetricGluing.Total Pieces) = a side := by
      rcases (members ⟨b.1, c⟩).mp relation with roof | gap
      · exact ⟨false, roof⟩
      · exact ⟨true, gap⟩
    obtain ⟨side, same⟩ := choose_side
    let patched : MetricGluing.Total Pieces := ⟨b.1, c⟩
    have patched_eq : patched = a side := same
    have package (k : MetricGluing.Total Pieces) (same_tag : k.1 = b.1)
        (distance : edist (same_tag ▸ k.2) b.2 < ENNReal.ofReal r) :
        ∃ x : Metric.eball k.2 (ENNReal.ofReal ρ),
          (⟨k.1, x.val⟩ : MetricGluing.Total Pieces) = b ∧
            edist x.val k.2 < ENNReal.ofReal r := by
      obtain ⟨i, b⟩ := b
      obtain ⟨j, k⟩ := k
      change j = i at same_tag
      subst j
      have near := (edist_comm _ _).trans_lt distance
      exact ⟨⟨b, near.trans_le (ENNReal.ofReal_le_ofReal small)⟩, rfl, near⟩
    have packed := package patched rfl close
    have named : ∃ x : Metric.eball (a side).2 (ENNReal.ofReal ρ),
        (⟨(a side).1, x.val⟩ : MetricGluing.Total Pieces) = b ∧
          edist x.val (a side).2 < ENNReal.ofReal r := patched_eq ▸ packed
    obtain ⟨x, equal, fit⟩ := named
    exact ⟨side, x, equal, fit⟩
  let mark (side : Bool) (t : unitInterval) (b : Bool) : MetricGluing.Total Pieces :=
    ⟨(a b).1, on_mark b side t⟩
  have source_slots (t : unitInterval) :
      let first := (⟨edge, 0⟩ : MetricGluing.BankStackSlot Stack)
      let last := (⟨edge, Fin.last (Stack edge).length⟩ : MetricGluing.BankStackSlot Stack)
      (L first t = mark false t false ∧ Rgt first t = mark false t true) ∧
      (L last t = mark true t true ∧ Rgt last t = mark true t false) :=
    ⟨MetricGluing.bankStack_singleton_first Pieces Stack Base Gap edge event invariant t member,
      MetricGluing.bankStack_singleton_last Pieces Stack Base Gap edge event invariant t member⟩
  have glued (side : Bool) (t : unitInterval) :
      MetricGluing.point Pieces Banks (mark side t false) =
        MetricGluing.point Pieces Banks (mark side t true) := by
    obtain ⟨⟨firstL, firstR⟩, ⟨lastL, lastR⟩⟩ := source_slots t
    let toPoint := MetricGluing.point Pieces Banks
    cases side
    · exact (congrArg toPoint firstL).symm.trans
        ((MetricGluing.bankStack_seam Pieces Stack Base Gap edge 0 t).trans
          (congrArg toPoint firstR))
    · exact (congrArg toPoint lastR).symm.trans
        ((MetricGluing.bankStack_seam Pieces Stack Base Gap edge
          (Fin.last (Stack edge).length) t).symm.trans (congrArg toPoint lastL))
  have trace (b side : Bool) (t : unitInterval) (x : Metric.eball (a b).2 (ENNReal.ofReal ρ))
      (equal : MetricGluing.SectorPairChart.pairTag a b x = mark side t b) :
      (A.chart b x).val.val = ray side (t.val * ell) := by
    have h : x.val = on_mark b side t := eq_of_heq (Sigma.mk.inj equal).2
    have y : edist (on_mark b side t) (a b).2 < ENNReal.ofReal ρ :=
      (congrArg (edist · (a b).2) h).symm.trans_lt x.property
    have arg : x = ⟨on_mark b side t, y⟩ := Subtype.ext h
    exact (congrArg (fun z => (A.chart b z).val.val) arg).trans (coordinates b side t y)
  have tag_eq (b c side : Bool) (t : unitInterval)
      (x : Metric.eball (a b).2 (ENNReal.ofReal ρ))
      (equal : MetricGluing.SectorPairChart.pairTag a b x = mark side t c) : b = c := by
    have tag := congrArg (fun z : MetricGluing.Total Pieces => z.1) equal
    cases b <;> cases c
    · rfl
    · cases tag
    · cases tag
    · rfl
  have trace_mark (b c side : Bool) (t : unitInterval)
      (x : Metric.eball (a b).2 (ENNReal.ofReal ρ))
      (equal : MetricGluing.SectorPairChart.pairTag a b x = mark side t c) :
      (A.chart b x).val.val = ray side (t.val * ell) := by
    have same := tag_eq b c side t x equal
    subst c
    exact trace b side t x equal
  have projection_near (b : Bool) (x : Metric.eball (a b).2 (ENNReal.ofReal ρ)) :
      edist (MetricGluing.point Pieces Banks (a false))
        (MetricGluing.point Pieces Banks (MetricGluing.SectorPairChart.pairTag a b x)) <
          ENNReal.ofReal rSlots := by
    have same : MetricGluing.point Pieces Banks (a false) = MetricGluing.point Pieces Banks (a b) :=
      MetricGluing.point_eq_of_eqvGen Pieces ((members (a b)).mpr (by
        cases b
        · exact Or.inl rfl
        · exact Or.inr rfl))
    have intrinsic := (MetricGluing.edist_of_le Pieces Banks (a b).1 (a b).2 x.val).trans_lt
      ((edist_comm _ _).trans_lt x.property)
    have bound := (congrArg (fun z => edist z
      (MetricGluing.point Pieces Banks (MetricGluing.SectorPairChart.pairTag a b x))) same).trans_lt
        intrinsic
    exact bound.trans_le (ENNReal.ofReal_le_ofReal ρslots)
  have compatible (b c : Bool) (x : Metric.eball (a b).2 (ENNReal.ofReal ρ))
      (y : Metric.eball (a c).2 (ENNReal.ofReal ρ))
      (joined : Banks (MetricGluing.SectorPairChart.pairTag a b x)
        (MetricGluing.SectorPairChart.pairTag a c y)) :
      (A.chart b x).val.val = (A.chart c y).val.val := by
    obtain ⟨⟨location, slot⟩, t, left, right⟩ := joined
    let seam : MetricGluing.BankStackSlot Stack := ⟨location, slot⟩
    let toPoint := MetricGluing.point Pieces Banks
    have endpoint : toPoint (MetricGluing.SectorPairChart.pairTag a b x) =
        toPoint (L seam t) := congrArg toPoint left
    have close : edist (toPoint RoofPoint[event]) (toPoint (L seam t)) <
        ENNReal.ofReal rSlots :=
      (congrArg (edist (toPoint RoofPoint[event])) endpoint).symm.trans_lt (projection_near b x)
    have same : location = edge := slots seam t close
    subst location
    obtain ⟨⟨firstL, firstR⟩, ⟨lastL, lastR⟩⟩ := source_slots t
    let leftOf (i : Fin ((Stack edge).length + 1)) := L ⟨edge, i⟩ t
    let rightOf (i : Fin ((Stack edge).length + 1)) := Rgt ⟨edge, i⟩ t
    have alternatives : slot = 0 ∨ slot = Fin.last (Stack edge).length :=
      MetricGluing.bankStack_singleton_slot_cases Stack edge event invariant slot
    rcases alternatives with first | last
    · exact (trace_mark b false false t x
        (left.trans ((congrArg leftOf first).trans firstL))).trans
        (trace_mark c true false t y
          (right.trans ((congrArg rightOf first).trans firstR))).symm
    · exact (trace_mark b true true t x
        (left.trans ((congrArg leftOf last).trans lastL))).trans
        (trace_mark c false true t y
          (right.trans ((congrArg rightOf last).trans lastR))).symm
  have shared := A.shared_of_bankRays on_mark ρgap distance coordinates glued
  exact A.hasMetricBallChart compatible shared near_tags

end Unfoldings.ConvexRoof
