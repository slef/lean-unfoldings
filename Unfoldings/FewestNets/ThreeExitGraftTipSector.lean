module

public import Unfoldings.FewestNets.ThreeExitGraftBendMarks
public import Unfoldings.Roof.PotentialContourFanAngles
public import Unfoldings.Roof.PotentialContourGapVertexMarks
public import Unfoldings.Roof.PotentialContourGapSectors
public import Unfoldings.Geometry.OrientedBankGapBendParameters
public import Unfoldings.Cone.MarkedSectorGerm



/-! The original marked sector at an actual source tip. -/

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

local instance graftTipSectorIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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
local notation "SourceOf[" e "]" => TriangleComplex.positiveContourVertex D Selection S.contour e
local notation "Nonroot[" e "]" => TriangleComplex.positiveContourVertex_nonroot D Selection S.contour e
local notation "SourceBank[" e "]" => FiniteBank[SourceOf[e],Nonroot[e]]
local notation "Length[" e "]" => TriangleComplex.boundaryBankLength D
  (TriangleComplex.contourParentBank D Selection S.contour (PotentialCutForest.boundary_roots Fcut)
    S.starts SourceOf[e] Nonroot[e] false)

include L in
/-- The chart of the true source tip keeps the two marks in their oriented bank order. -/
theorem contourGraftTip_markedSectorGerm (e : Event) (member : e ∈ Stack SourceBank[e]) :
    let κ := (D).interiorAngularDefect Set.univ SourceOf[e]
    Nonempty (MarkedSectorGerm ((Model[e]).edgePoint false 0 0) κ
      (fun side t => Gap SourceBank[e] e member (!side) t) (fun _ => Length[e])) := by
  let gap := S.gaps e
  let d := (BankAt[e]).chain.edge 0
  let κ := (D).interiorAngularDefect Set.univ SourceOf[e]
  let x := (Model[e]).edgePoint false 0 0
  let mark (side : Bool) (t : unitInterval) := Gap SourceBank[e] e member (!side) t
  let ell := Length[e]
  have distance (side : Bool) (t : unitInterval) :
      edist (mark side t) x = ENNReal.ofReal (t.val * ell) := by
    have h := L.edist_contourGapMark_eq_length S SourceOf[e] Nonroot[e] e member (!side) t 0
    rw [(Fcut).contourGapMark_at_source S.contour S.starts S.gaps e member (!side), edist_dist] at h
    change edist (mark side t) x = ENNReal.ofReal ell * ENNReal.ofReal (dist t.val 0) at h
    rw [h, Real.dist_eq, sub_zero, abs_of_nonneg t.property.1,
      ENNReal.ofReal_mul t.property.1, mul_comm]
  have address (side : Bool) (t : unitInterval) : mark side t = (Model[e]).edgePoint side 0 t := by
    simpa only [Bool.not_not] using
      (Fcut).contourGapMark_source_edge S.contour S.starts S.gaps e member (!side) t
  have speed : ‖d‖ = ell := by
    let c := (Fcut).contourSourceBankChain S.contour S.starts e
    change ‖((D).boundaryChainRoll c).edge 0‖ = ell
    rw [(D).boundaryChainRoll_edge_length]
    have raw := (Fcut).contourSourceBankChain_germ S.contour S.starts e 0
    exact congrArg (fun germ : (D).Germ => dist (((D).triangle germ.1.1).vertex
      ((D).germFarCorner germ).2) (((D).triangle germ.1.1).vertex germ.1.2)) raw
  have tip := (Fcut).contourSource_gap_tip_chart S.contour S.starts e gap
  change 0 < ‖d‖ ∧ _ at tip
  rw [speed] at tip
  obtain ⟨positive, chart, trace⟩ := tip
  have center : (chart ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val =
      closedAngularSectorOrigin e.property.2.le := by
    apply PolygonalPoint.ext
    exact (trace false 0 (Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive))).trans
      (by simp [closedAngularSectorOrigin])
  refine ⟨⟨⟨e.property.2, ell, positive, chart, center⟩, distance, ?_⟩⟩
  intro side t near
  have physical_near : edist ((Model[e]).edgePoint side 0 t) x < ENNReal.ofReal ell :=
    (congrArg (edist · x) (address side t)).symm.trans_lt near
  have eq : (⟨mark side t, near⟩ : Metric.eball x (ENNReal.ofReal ell)) =
      ⟨(Model[e]).edgePoint side 0 t, physical_near⟩ := Subtype.ext (address side t)
  change (chart ⟨mark side t, near⟩).val.val = (t.val * ell) • polarRay (if side then κ else 0)
  rw [eq, trace]
  cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true,
    polarRay_zero, Complex.real_smul, mul_one] <;> rfl

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
