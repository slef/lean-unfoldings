module

public import Unfoldings.FewestNets.ThreeExitContourGraft
public import Unfoldings.Geometry.BankGapClosedEmbeddings

/-! Both sides of every ordered attachment retain one exact physical interval metric. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel

universe u v

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

local instance graftMetricIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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
local notation "restore" =>
  SpatialEnvelope.WholePartition.restoreCut L.whole.partition R.wholeCarrier
local notation "Attachment" => PotentialCutForest.ContourAttachment Fcut
local notation "Param" => PotentialCutForest.contourAttachmentParameter Fcut
local notation "Path[" e "]" => PotentialCutForest.contourSourceSpatialRay Fcut S.contour S.starts e
local notation "Bank[" e "]" => PotentialCutForest.contourSourceBankChain Fcut S.contour S.starts e
local notation "Length[" e "]" => TriangleComplex.positiveContourBankLength D Selection S.contour e
local notation "Q" => SpatialEnvelope.FloorMesh.roof T
  (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M S.higher)
local notation "Fold" => contourGraftPieceCollapse L S

/-- Each finite or continued attachment uses its standard interval metric. -/
@[instance_reducible]
def contourAttachmentMetric (edge : Attachment) : MetricSpace (Param edge) :=
  match edge with
  | .inl _ => inferInstanceAs (MetricSpace unitInterval)
  | .inr _ => inferInstanceAs (MetricSpace ℝ≥0)

/-- The metric of any original base attachment is exactly its physical chord metric. -/
theorem edist_contourBaseMark_eq_spatial (e : Attachment) (side : Bool) (s t : Param e) :
    edist (Base e side s) (Base e side t) =
      edist (restore (Base e side s)).val (restore (Base e side t)).val := by
  cases e with
  | inl v =>
    let bank := (D).contourParentBank Selection S.contour
      (Fcut).boundary_roots S.starts v.val v.property side
    let x := (D).directedBoundaryPath bank s
    let y := (D).directedBoundaryPath bank t
    change edist (L.fineMeshWholeMap S.higher x) (L.fineMeshWholeMap S.higher y) =
      edist (restore (L.fineMeshWholeMap S.higher x)).val
        (restore (L.fineMeshWholeMap S.higher y)).val
    exact (L.fineMeshWholeMap_edist_bank S.higher bank s t).trans
      (((T).pairedFolding.edist_directedBoundaryPath_eq_spatial bank s t).trans
        (congrArg₂ (fun u v : Space => edist u v)
          (L.restore_fineMeshWholeMap S.higher x) (L.restore_fineMeshWholeMap S.higher y)).symm)
  | inr e => exact (L.contourTerminalContinuation S.higher S.contour S.starts e).spatial_edist side s t

/-- Both original base sides have the same intrinsic interval metric. -/
theorem edist_contourBaseMark_sides (e : Attachment) (side : Bool) (s t : Param e) :
    edist (Base e side s) (Base e side t) = edist (Base e false s) (Base e false t) := by
  rw [L.edist_contourBaseMark_eq_spatial, L.edist_contourBaseMark_eq_spatial]
  cases side
  · rfl
  · rw [L.restore_contourBaseMark_sides S e s, L.restore_contourBaseMark_sides S e t]

private theorem norm_gap_chain_edge_eq_spatial (e : Event) (i : Fin (Length[e] + 1)) (side : Bool) :
    ‖(Model[e].bank side).chain.edge i‖ = ‖(Path[e]).chain.edge i‖ := by
  have physical : ‖(Path[e]).chain.edge i‖ = (D).boundaryBankLength ((Bank[e]).point i) := by
    change ‖((Q).folding.boundarySpatialChain Bank[e]).edge i‖ = _
    rw [(Q).folding.boundarySpatialChain_edge]
    exact ((Q).folding.boundaryBankLength_eq_germDirection_norm _).symm
  cases side
  · change ‖((D).boundaryChainRoll Bank[e]).edge i‖ = _
    rw [(D).boundaryChainRoll_edge_length, physical]
  · change ‖(((Fcut).contourSourceRay S.contour S.starts e).rotateSuffix 0 _).chain.edge i‖ = _
    rw [PolygonalRay.rotateSuffix_zero_edge]
    apply (LinearIsometry.norm_map _ _).trans
    rw [physical]
    exact (D).boundaryChainRoll_edge_length Bank[e] i

/-- Every developed gap edge has its nonzero original physical length. -/
theorem contourGap_edge_ne_zero (e : Event) (side : Bool) (i : Fin (Length[e] + 1)) :
    (Model[e].bank side).chain.edge i ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_gap_chain_edge_eq_spatial S]
  exact norm_ne_zero_iff.mpr ((Fcut).contourSourceSpatialRay_edge_ne_zero S.contour S.starts e i)

private theorem edist_source_path_finite (e : Event) (i : Fin (Length[e] + 1))
    (s t : unitInterval) :
    edist ((Path[e]).chain.point i s) ((Path[e]).chain.point i t) =
      (‖(Path[e]).chain.edge i‖₊ : ℝ≥0∞) * edist s t := by
  simp only [PolygonalChain.point, AffineMap.lineMap_apply_module']
  rw [edist_dist, edist_dist, dist_eq_norm, add_sub_add_right_eq_sub, ← sub_smul,
    norm_smul, Real.norm_eq_abs]
  change ENNReal.ofReal (|s.val - t.val| * ‖(Path[e]).chain.edge i‖) = _
  rw [ENNReal.ofReal_mul (abs_nonneg _), mul_comm, ofReal_norm, enorm_eq_nnnorm]
  rfl

private theorem edist_source_path_tail (e : Event) (s t : ℝ≥0) :
    edist ((Path[e]).tail s) ((Path[e]).tail t) =
      (‖(Path[e]).direction‖₊ : ℝ≥0∞) * edist s t := by
  rw [PolygonalRay.tail, PolygonalRay.tail, edist_dist, edist_dist, dist_eq_norm,
    add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs,
    ENNReal.ofReal_mul (abs_nonneg _), mul_comm, ofReal_norm, enorm_eq_nnnorm]
  rfl

theorem contourGraftGap_direction_eq_last (e : Event) (side : Bool) :
    (Model[e].bank side).direction = (Model[e].bank side).chain.edge (Fin.last (Length[e])) := by
  cases side
  · rfl
  · change (((Fcut).contourSourceRay S.contour S.starts e).rotateSuffix 0 _).direction =
      (((Fcut).contourSourceRay S.contour S.starts e).rotateSuffix 0 _).chain.edge _
    rw [PolygonalRay.rotateSuffix_zero_edge]
    rfl

/-- Each individual gap bank has the same interval distances as its physical trace. -/
theorem edist_contourGapMark_eq_spatial (a : Attachment) (e : Event)
    (member : e ∈ Stack a) (side : Bool) (s t : Param a) :
    edist (Gap a e member side s) (Gap a e member side t) =
      edist (Fold (some e) (Gap a e member side s)) (Fold (some e) (Gap a e member side t)) := by
  cases a with
  | inl v =>
    let i := (D).contourGapBankIndex Selection S.contour v.val v.property e
      (((D).mem_contourEdgeGapStack Selection S.contour v.val e).mpr
        (((D).mem_contourSavedGapStack Selection S.contour v.val e).mp member))
    change edist (Model[e].edgePoint (!side) i s) (Model[e].edgePoint (!side) i t) =
      edist (R.contourSourceGapCollapse level M S.higher S.contour S.starts e (S.gaps e)
        (Model[e].edgePoint (!side) i s)).val
        (R.contourSourceGapCollapse level M S.higher S.contour S.starts e (S.gaps e)
          (Model[e].edgePoint (!side) i t)).val
    rw [R.contourSourceGapCollapse_edgePoint, R.contourSourceGapCollapse_edgePoint,
      Model[e].edist_edgePoint, edist_source_path_finite S]
    have speed : ‖(Model[e].bank (!side)).chain.edge i‖₊ = ‖(Path[e]).chain.edge i‖₊ :=
      Subtype.ext (norm_gap_chain_edge_eq_spatial S e i (!side))
    rw [speed]
  | inr edge =>
    change edist (Model[e].tailPoint (!side) s) (Model[e].tailPoint (!side) t) =
      edist (R.contourSourceGapCollapse level M S.higher S.contour S.starts e (S.gaps e)
        (Model[e].tailPoint (!side) s)).val
        (R.contourSourceGapCollapse level M S.higher S.contour S.starts e (S.gaps e)
          (Model[e].tailPoint (!side) t)).val
    rw [R.contourSourceGapCollapse_tailPoint, R.contourSourceGapCollapse_tailPoint,
      Model[e].edist_tailPoint, edist_source_path_tail S, contourGraftGap_direction_eq_last S]
    have speed : ‖(Model[e].bank (!side)).chain.edge (Fin.last (Length[e]))‖₊ = ‖(Path[e]).direction‖₊ :=
      Subtype.ext (norm_gap_chain_edge_eq_spatial S e (Fin.last (Length[e])) (!side))
    rw [speed]

/-- Consecutive bank slots use one common intrinsic interval metric. -/
theorem edist_contourGapMark_eq_base (a : Attachment) (e : Event)
    (member : e ∈ Stack a) (side : Bool) (s t : Param a) :
    edist (Gap a e member side s) (Gap a e member side t) =
      edist (Base a false s) (Base a false t) := by
  rw [L.edist_contourGapMark_eq_spatial S, L.contourGraftPieceCollapse_gap_eq S,
    L.contourGraftPieceCollapse_gap_eq S, ← L.edist_contourBaseMark_eq_spatial S]
  exact L.edist_contourBaseMark_sides S a side s t

/-- All finite and infinite base banks are closed, embedded intervals. -/
theorem isClosedEmbedding_contourBaseMark (e : Attachment) (side : Bool) :
    letI : MetricSpace (Param e) := contourAttachmentMetric S e
    Topology.IsClosedEmbedding (Base e side) := by
  cases e with
  | inl v =>
    apply (L.continuous_contourParentMark S.higher S.contour S.starts v.val v.property side
      ).isClosedEmbedding
    intro s t same
    have first := L.horizontal_contourParentMark S.higher S.contour S.starts v.val v.property side s
    have last := L.horizontal_contourParentMark S.higher S.contour S.starts v.val v.property side t
    have distinct : (Q).projectedVertex v.val ≠
        (Q).projectedVertex ((Fcut).parents.parent v.val) := by
      intro equal
      exact ((Fcut).parents.ascending v.val v.property).ne
        (congrArg (Fcut).parents.height ((Q).projectedVertex_injective equal))
    have aligned := congrArg (fun y => Cap.horizontal (restore y).val) same
    exact Subtype.ext ((AffineMap.lineMap_injective ℝ distinct)
      (first.symm.trans (aligned.trans last)))
  | inr e =>
    exact Dilation.isClosedEmbedding ((L.contourTerminalContinuation S.higher S.contour S.starts e).mark side)

/-- The gap copies of every finite and infinite bank are also closed embeddings. -/
theorem isClosedEmbedding_contourGapMark (a : Attachment) (e : Event)
    (member : e ∈ Stack a) (side : Bool) :
    letI : MetricSpace (Param a) := contourAttachmentMetric S a
    Topology.IsClosedEmbedding (Gap a e member side) := by
  have edge_ne (i : Fin (Length[e] + 1)) : (Model[e].bank (!side)).chain.edge i ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_gap_chain_edge_eq_spatial S]
    exact norm_ne_zero_iff.mpr ((Fcut).contourSourceSpatialRay_edge_ne_zero S.contour S.starts e i)
  cases a with
  | inl v => exact Model[e].edgePoint_isClosedEmbedding (!side) _ (edge_ne _)
  | inr edge =>
    apply Model[e].tailPoint_isClosedEmbedding
    rw [contourGraftGap_direction_eq_last S]
    exact edge_ne _

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
