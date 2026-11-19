module

public import Unfoldings.Cone.SectorPairBankRays

public import Unfoldings.Cone.DirectedIntervalChart
public import Unfoldings.Roof.CompatibleContourSourceOnlyLeaf
public import Unfoldings.Roof.CompatibleMeshCornerCharts

/-! The actual whole roof corner at a positive leaf, ordered by its two banks. -/

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

local instance contourLeafRoofChartFintype : Fintype (T).Index :=
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

local instance contourLeafRoofChartWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "Retain" => PotentialCutForest.retain Fcut
local notation "VertexAt[" w "]" => TriangleComplex.vertexPoint D Retain w
local notation "Height[" x "]" => SlopeEnvelope.height (K.clippedExtension slopes compact nonempty)
  (Cap.horizontal (SpatialFolding.toSpace
    (SpatialEnvelope.Triangulation.pairedFolding
      (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) Retain x))
local notation "BankAt[" e "," side "]" => TriangleComplex.contourParentBank D Selection contour
  (PotentialCutForest.boundary_roots Fcut) starts (Subtype.val e) (Subtype.property e) side

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "SourceOf[" e "]" => TriangleComplex.positiveContourVertex D Selection contour e
/-- The whole roof at a positive leaf has the complement of its own gap defect.
The exit bank is on the positive axis and the entrance bank is on the terminal ray. -/
theorem compatibleContourSourceOnlyLeaf_roof_sector_chart (event : Event)
    (nonroot : SourceOf[event] ∉ (Fcut).parents.roots)
    (childless : ∀ v ∉ (Fcut).parents.roots, (Fcut).parents.parent v ≠ SourceOf[event]) :
    let edge := (⟨SourceOf[event], nonroot⟩ :
      {w : (D).Vertex Set.univ // w ∉ (Fcut).parents.roots})
    let p := BankAt[edge,false]
    let q := BankAt[edge,true]
    let w := (D).boundaryEndVertex Retain p
    let θ := (D).totalAngle Retain w
    let x := Map VertexAt[w]
    θ + (D).interiorAngularDefect Set.univ SourceOf[event] = 2 * Real.pi ∧
    Base (.inl edge) false 0 = x ∧ Base (.inl edge) true 0 = x ∧
    ∃ r : ℝ, 0 < r ∧
      ∃ chart : Metric.eball x (ENNReal.ofReal r) ≃ᵢ
          Metric.eball (closedAngularSectorOrigin ((D).totalAngle_pos Retain w).le)
            (ENNReal.ofReal r),
        (∀ (t : unitInterval) (near : edist (Base (.inl edge) false t) x < ENNReal.ofReal r),
          (chart ⟨Base (.inl edge) false t, near⟩).val.val =
            (t.val * (D).boundaryBankLength p : ℝ)) ∧
        (∀ (t : unitInterval) (near : edist (Base (.inl edge) true t) x < ENNReal.ofReal r),
          (chart ⟨Base (.inl edge) true t, near⟩).val.val =
            (t.val * (D).boundaryBankLength q) • polarRay θ) := by
  dsimp only
  let edge := (⟨SourceOf[event], nonroot⟩ :
    {w : (D).Vertex Set.univ // w ∉ (Fcut).parents.roots})
  let p := BankAt[edge,false]
  let q := BankAt[edge,true]
  let w := (D).boundaryEndVertex Retain p
  obtain ⟨_, w', _, below, balance, endpoints⟩ :=
    K.compatibleContourSourceOnlyLeaf_roof_fan compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W event nonroot childless
  have end_at (side : Bool) : (D).boundaryEndVertex Retain BankAt[edge,side] = w' := by
    have classified :=
      (K.compatibleContourRoofVertex_eq_parentMark_iff compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W w' below edge side 0).mp
        (endpoints side)
    rcases classified with ⟨_, start⟩ | ⟨one, _⟩
    · exact start.symm
    · exact (zero_ne_one one).elim
  have same : w' = w := (end_at false).symm
  subst w'
  have mate : (D).boundaryMate Retain p = q :=
    ((D).exists_unique_other_boundaryEnd Retain p).unique ((D).boundaryMate_spec Retain p)
      ⟨((D).contourParentBank_distinct Selection contour (Fcut).boundary_roots starts
        edge.val nonroot).symm, end_at true⟩
  have small : (D).totalAngle Retain w < 2 * Real.pi := by
    have pos : 0 < (D).interiorAngularDefect Set.univ SourceOf[event] := event.property.2
    linarith
  have speeds (b : (D).BoundaryEnd Retain) (at_vertex : (D).boundaryEndVertex Retain b = w)
      (t : unitInterval) :
      ENNReal.ofReal (t.val * (D).boundaryBankLength b) =
        edist (Map ((D).directedBoundaryPath b t)) (Map VertexAt[w]) := by
    have start : (D).directedBoundaryPath b 0 = VertexAt[w] :=
      ((D).directedBoundaryPath_zero b).trans (congrArg ((D).vertexPoint Retain) at_vertex)
    calc
      _ = ENNReal.ofReal ((D).boundaryBankLength b) * edist t (0 : unitInterval) := by
        rw [mul_comm t.val, ENNReal.ofReal_mul ((D).boundaryBankLength_pos b).le, edist_dist]
        congr 1
        apply congrArg ENNReal.ofReal
        change t.val = dist t.val 0
        rw [Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]
      _ = _ :=
        (((T).pairedFolding.edist_directedBoundaryPath_eq_length b t 0).symm.trans
          (K.compatibleWholeMap_edist_bank compact nonempty R no_boundary level higher M
            positive inner_disk beta acute W b t 0).symm).trans
          (congrArg (fun z => edist (Map ((D).directedBoundaryPath b t)) (Map z)) start)
  obtain ⟨r, rpos, chart, first, last⟩ := (D).exists_directedIntervalChart Retain p Map small
    speeds (K.compatibleMesh_corner_fan_chart compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W w below)
  refine ⟨balance, endpoints false, endpoints true, r, rpos, chart, first, ?_⟩
  have finish := last
  rw [mate] at finish
  exact finish

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "FirstEdge[" e "]" => (Sum.inl
  (Subtype.mk SourceOf[e] (TriangleComplex.positiveContourVertex_nonroot D Selection contour e)) :
    Attachment)

local notation "Parent[" v "," h "," side "]" => TriangleComplex.contourParentBank D Selection
  contour (PotentialCutForest.boundary_roots Fcut) starts v h side

private theorem leaf_parent_bank_speed (v : (D).Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots)
    (side : Bool) :
    (D).boundaryBankLength Parent[v,nonroot,side] =
      (D).boundaryBankLength Parent[v,nonroot,false] := by
  let F := (T).pairedFolding
  let bank (b : Bool) := Parent[v,nonroot,b]
  have same := (F.contourParentBank_direction Selection contour (Fcut).boundary_roots starts
    v nonroot side).trans
      (F.contourParentBank_direction Selection contour (Fcut).boundary_roots starts
        v nonroot false).symm
  exact (F.boundaryBankLength_eq_germDirection_norm (bank side)).trans
    ((congrArg norm same).trans (F.boundaryBankLength_eq_germDirection_norm (bank false)).symm)

private theorem leaf_roof_mark_distance (event : Event)
    (other_start : Base FirstEdge[event] true 0 = (Base FirstEdge[event] false 0)) :
    let v := SourceOf[event]
    let p := Parent[v,(D).positiveContourVertex_nonroot Selection contour event,false]
    ∀ side (t : unitInterval), edist (Base FirstEdge[event] side t) (Base FirstEdge[event] false 0) =
      ENNReal.ofReal (t.val * (D).boundaryBankLength p) := by
  let v := SourceOf[event]
  let nonroot := (D).positiveContourVertex_nonroot Selection contour event
  let edge := FirstEdge[event]
  let p (side : Bool) := Parent[v,nonroot,side]
  let ell := (D).boundaryBankLength (p false)
  have ellpos : 0 < ell := (D).boundaryBankLength_pos (p false)
  have roof_speed (side : Bool) : (D).boundaryBankLength (p side) = ell :=
    leaf_parent_bank_speed K compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts v nonroot side
  have time_dist (t : unitInterval) : edist t (0 : unitInterval) = ENNReal.ofReal t.val := by
    rw [edist_dist]
    apply congrArg ENNReal.ofReal
    change dist t.val 0 = t.val
    rw [Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]
  have distance_roof (side : Bool) (t : unitInterval) :
      edist (Base edge side t) (Base FirstEdge[event] false 0) = ENNReal.ofReal (t.val * ell) := by
    have start (b : Bool) : Base edge b 0 = (Base FirstEdge[event] false 0) := by
      cases b
      · rfl
      · exact other_start
    let begin := (D).directedBoundaryPath (p side) (0 : unitInterval)
    let finish := (D).directedBoundaryPath (p side) t
    calc
      _ = edist (Base edge side t) (Base edge side 0) :=
        congrArg (edist (Base edge side t)) (start side).symm
      _ = edist finish begin :=
        K.compatibleWholeMap_edist_bank compact nonempty R no_boundary level higher M
          positive inner_disk beta acute W (p side) t 0
      _ = ENNReal.ofReal ((D).boundaryBankLength (p side)) * edist t (0 : unitInterval) :=
        (T).pairedFolding.edist_directedBoundaryPath_eq_length (p side) t 0
      _ = _ := by rw [roof_speed, time_dist, mul_comm t.val ell, ENNReal.ofReal_mul ellpos.le]
  exact distance_roof

-- Transport the marked chart without reducing the intrinsic whole-cut construction.
omit beta acute in
private theorem exists_centered_chart_of_mark_coordinates
    {X : Type*} [EMetricSpace X] {p : X} {θ r : ℝ} (angle : 0 ≤ θ) (rpos : 0 < r)
    (mark : Bool → unitInterval → X) (h : mark false 0 = p)
    (coord : Bool → unitInterval → ℂ) (zero : coord false 0 = 0)
    (chart : Metric.eball p (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (closedAngularSectorOrigin angle) (ENNReal.ofReal r))
    (ray : ∀ (b : Bool) (t : unitInterval)
      (near : edist (mark b t) p < ENNReal.ofReal r),
      (chart ⟨mark b t, near⟩).val.val = coord b t) :
    ∃ A : Metric.eball (mark false 0) (ENNReal.ofReal r) ≃ᵢ
        Metric.eball (closedAngularSectorOrigin angle) (ENNReal.ofReal r),
      (A ⟨mark false 0, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)⟩).val =
        closedAngularSectorOrigin angle ∧
      ∀ (b : Bool) (t : unitInterval) (near : edist (mark b t) (mark false 0) < ENNReal.ofReal r),
        (A ⟨mark b t, near⟩).val.val = coord b t := by
  subst p
  refine ⟨chart, PolygonalPoint.ext ?_, ray⟩
  exact (ray false 0 (Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos))).trans zero

set_option maxHeartbeats 180000 in
-- The original whole-cut metric appears in the marked bank transport.
/-- The positive leaf chart is centered on its outgoing mark and calibrated on both banks. -/
theorem compatibleContourSourceOnlyLeaf_roof_marked_chart
    (event : Event)
    (childless : ∀ v ∉ (Fcut).parents.roots, (Fcut).parents.parent v ≠ SourceOf[event]) :
    let edge := FirstEdge[event]
    let v := SourceOf[event]
    let p := Parent[v,(D).positiveContourVertex_nonroot Selection contour event,false]
    let w := (D).boundaryEndVertex Retain p
    let θ := (D).totalAngle Retain w
    let ell := (D).boundaryBankLength p
    ∃ (θpos : 0 < θ) (r : ℝ) (rpos : 0 < r)
      (chart : Metric.eball (Base FirstEdge[event] false 0) (ENNReal.ofReal r) ≃ᵢ
        Metric.eball (closedAngularSectorOrigin θpos.le) (ENNReal.ofReal r)),
      θ + (D).interiorAngularDefect Set.univ v = 2 * Real.pi ∧
      (chart ⟨(Base FirstEdge[event] false 0),
        Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)⟩).val =
          closedAngularSectorOrigin θpos.le ∧
      (∀ side (t : unitInterval),
        edist (Base edge side t) (Base FirstEdge[event] false 0) = ENNReal.ofReal (t.val * ell)) ∧
      ∀ side (t : unitInterval)
        (near : edist (Base edge side t) (Base FirstEdge[event] false 0) < ENNReal.ofReal r),
        (chart ⟨Base edge side t, near⟩).val.val =
          MetricGluing.SectorPairChart.bankRay θ side (t.val * ell) := by
  let v := SourceOf[event]
  let nonroot := (D).positiveContourVertex_nonroot Selection contour event
  let edge := FirstEdge[event]
  let p (side : Bool) := Parent[v,nonroot,side]
  let w := (D).boundaryEndVertex Retain (p false)
  let θ := (D).totalAngle Retain w
  let ell := (D).boundaryBankLength (p false)
  have roof_speed (side : Bool) : (D).boundaryBankLength (p side) = ell :=
    leaf_parent_bank_speed K compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts v nonroot side
  have θpos : 0 < θ := (D).totalAngle_pos Retain w
  obtain ⟨complement, roof_start, roof_end, rRoof, roof_pos, roof, roof_first, roof_last⟩ :=
    K.compatibleContourSourceOnlyLeaf_roof_sector_chart compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W event nonroot childless
  let xRoof := Map VertexAt[w]
  have hRoof : (Base FirstEdge[event] false 0) = xRoof := roof_start
  have hRoofEnd : Base edge true 0 = (Base FirstEdge[event] false 0) := roof_end.trans hRoof.symm
  let marks := Base edge
  let ray (side : Bool) (t : unitInterval) :=
    MetricGluing.SectorPairChart.bankRay θ side (t.val * ell)
  have coords (side : Bool) (t : unitInterval)
      (near : edist (marks side t) xRoof < ENNReal.ofReal rRoof) :
      (roof ⟨marks side t, near⟩).val.val = ray side t := by
    cases side
    · exact roof_first t near
    · calc
        _ = (t.val * (D).boundaryBankLength (p true)) • polarRay θ := roof_last t near
        _ = (t.val * ell) • polarRay θ :=
          congrArg (fun d : ℝ => (t.val * d) • polarRay θ) (roof_speed true)
        _ = ray true t := Complex.real_smul
  have zero : ray false 0 = 0 := by simp [ray, MetricGluing.SectorPairChart.bankRay]
  obtain ⟨chart, centered, coordinates⟩ :=
    exists_centered_chart_of_mark_coordinates θpos.le roof_pos marks hRoof ray zero roof coords
  have distance_roof := leaf_roof_mark_distance K compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W event hRoofEnd
  exact ⟨θpos, rRoof, roof_pos, chart, complement, centered, distance_roof, coordinates⟩

end Unfoldings.ConvexRoof
