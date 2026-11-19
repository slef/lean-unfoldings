module

public import Unfoldings.Roof.CompatibleContourParentMarkHalfPlane
public import Unfoldings.Roof.CompatibleContourBankEmbeddings
public import Unfoldings.Geometry.OrientedBankGapHalfPlane
public import Unfoldings.Metric.BankStackCurves

/-! Both original banks of each finite slot have normalized half-plane charts. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof

open MetricGluing

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

local instance contourFiniteBankChartMeshFintype : Fintype (T).Index :=
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
  (geometry : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    OrientedBankGap
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance contourFiniteBankChartWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Models" => fun event => OrientedBankGap.model (geometry event)

local notation "Pieces" => K.compatibleContourGraftPiece compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour starts W Models
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Base" => K.compatibleContourBaseMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W Models
local notation "Gap" => K.compatibleContourGapMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W Models

local notation "Vertex" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "SlotAt[" v "," i "]" => (Sigma.mk (Sum.inl v) i : BankStackSlot Stack)
local notation "BankAt[" v "," side "]" => TriangleComplex.contourParentBank D Selection contour
  (PotentialCutForest.boundary_roots Fcut) starts (Subtype.val v) (Subtype.property v) side

/-- A finite bank chart records the speed of the whole bank and the direction of its
coordinates in the local half-plane. -/
def FiniteBankChart {X : Type*} [EMetricSpace X]
    (bank : unitInterval → X) (t : unitInterval) (occupied : Bool) : Prop :=
  ∃ speed : ℝ, 0 < speed ∧
    (∀ s u, edist (bank s) (bank u) = ENNReal.ofReal speed * edist s u) ∧
    ∃ r, Nonempty (BankHalfPlaneChart bank t occupied (fun s => (s.val - t.val) * speed) r)

private theorem compatibleContourFiniteBase_chart
    (vertex : Vertex) (side occupied : Bool) (t : unitInterval) (bounds : 0 < t ∧ t < 1) :
    FiniteBankChart (Base (.inl vertex) side) t occupied := by
  let bank := BankAt[vertex,side]
  refine ⟨(D).boundaryBankLength bank, (D).boundaryBankLength_pos bank, ?_, ?_⟩
  · intro s u
    exact (K.compatibleWholeMap_edist_bank compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W bank s u).trans
        ((T).pairedFolding.edist_directedBoundaryPath_eq_length bank s u)
  · exact K.compatibleContourParentMark_normalized_chart compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W vertex.val vertex.property side
      occupied t bounds

private theorem compatibleContourFiniteGap_chart
    (vertex : Vertex) (event : Event) (member : event ∈ Stack (.inl vertex))
    (side occupied : Bool) (t : unitInterval) (bounds : 0 < t ∧ t < 1) :
    FiniteBankChart (Gap (.inl vertex) event member side) t occupied := by
  let i := (D).contourGapBankIndex Selection contour vertex.val vertex.property event
    (((D).mem_contourEdgeGapStack Selection contour vertex.val event).mpr
      (((D).mem_contourSavedGapStack Selection contour vertex.val event).mp member))
  let G := geometry event
  have genuine := K.compatibleContourGapBank_edge_ne_zero compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts (fun e => (geometry e).model) event
  let speed := ‖(G.model.bank side).chain.edge i‖
  refine ⟨speed, norm_pos_iff.mpr (genuine side i), ?_, ?_⟩
  · intro s u
    change edist (G.model.edgePoint side i s) (G.model.edgePoint side i u) =
      ENNReal.ofReal speed * edist s u
    simpa only [speed, ofReal_norm, enorm_eq_nnnorm] using G.model.edist_edgePoint side i s u
  · exact G.exists_model_edge_normalized_chart genuine side occupied i t bounds

/-- The two literal banks of any finite stack slot have oppositely occupied charts
at their original arclength speeds for all closed parameters. -/
theorem compatibleContourFiniteSlot_charts
    (vertex : Vertex) (i : Fin ((Stack (.inl vertex)).length + 1)) (t : unitInterval)
    (bounds : 0 < t ∧ t < 1) :
    let left := bankStackLeftCurve Stack Pieces Base Gap SlotAt[vertex,i]
    let right := bankStackRightCurve Stack Pieces Base Gap SlotAt[vertex,i]
    FiniteBankChart left t false ∧ FiniteBankChart right t true := by
  let slot := SlotAt[vertex,i]
  have base (side occupied : Bool) := K.compatibleContourFiniteBase_chart compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W geometry vertex
      side occupied t bounds
  have gap (event : Event) (member : event ∈ Stack (.inl vertex)) (side occupied : Bool) :=
    K.compatibleContourFiniteGap_chart compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W geometry vertex event member side occupied t bounds
  let P (occupied : Bool) (q : Σ j, unitInterval → Pieces j) := FiniteBankChart q.2 t occupied
  refine ⟨?_, ?_⟩
  · change P false (bankStackLeftData Stack Pieces Base Gap slot)
    unfold bankStackLeftData
    split
    · exact base false false
    · exact gap _ (List.getElem_mem _) true false
  · change P true (bankStackRightData Stack Pieces Base Gap slot)
    unfold bankStackRightData
    split
    · exact gap _ (List.getElem_mem _) false true
    · exact base true true

end Unfoldings.ConvexRoof
