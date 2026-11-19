module

public import Unfoldings.Roof.CompatibleContourJoinBankData

/-! Both original signed bank curves have matching closed half-plane charts. -/

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

local instance contourJoinedBankChartMeshFintype : Fintype (T).Index :=
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

local instance contourJoinedBankChartWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Models" => fun event => OrientedBankGap.model (geometry event)

local notation "Pieces" => K.compatibleContourGraftPiece compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour starts W Models
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Base" => K.compatibleContourBaseMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W Models
local notation "Gap" => K.compatibleContourGapMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W Models


local notation "Edge" => TriangleComplex.ContourTerminalEdge D Selection
local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour


local notation "Child[" e "]" => (Subtype.mk (Subtype.val e) (And.left (Subtype.property e)))

local notation "Data[" e "," i "," side "]" => K.compatibleContourJoinBankData compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts W geometry e i side
local notation "Join[" e "," i "," side "]" =>
  K.compatibleContourJoinedBank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W geometry e i side
local notation "Zero" => (Subtype.mk (0 : ℝ) (by norm_num) : BankJoinTime)

/-- One closed signed bank has its original speed and centered occupied half-plane. -/
def JoinBankChart {X : Type*} [EMetricSpace X] (bank : BankJoinTime → X)
    (occupied : Bool) : Prop :=
  IsClosed (Set.range bank) ∧ ∃ speed : ℝ, 0 < speed ∧
    (∀ s, edist (bank Zero) (bank s) = ENNReal.ofReal (|s.val| * speed)) ∧
    ∃ r, Nonempty (BankHalfPlaneChart bank Zero occupied (fun s => s.val * speed) r)

private theorem compatibleContourRoofJoin_chart
    (edge : Edge) (side occupied : Bool) :
    JoinBankChart (joinedBank (Base (.inl Child[edge]) side) (Base (.inr edge) side)) occupied := by
  let bank := (D).contourParentBank Selection contour (Fcut).boundary_roots starts edge.val
    edge.property.1 false
  have closed := K.compatibleContourBaseMark_isClosedEmbedding compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W Models
  have join := K.compatibleContourBaseMark_join compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W Models edge side
  refine ⟨?_, (D).boundaryBankLength bank, (D).boundaryBankLength_pos bank, ?_, ?_⟩
  · rw [joinedBank_range _ _ join.symm]
    exact (closed (.inl Child[edge]) side).isClosed_range.union
      (closed (.inr edge) side).isClosed_range
  · exact K.edist_compatibleContourRoofJoinBank compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W edge side
  · exact K.compatibleContourRoofJoinBank_normalized_chart compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W edge side occupied

private theorem compatibleContourGapJoin_chart (edge : Edge) (event : Event)
    (member : event ∈ Stack (.inr edge)) (side occupied : Bool) :
    JoinBankChart (joinedBank (Gap (.inl Child[edge]) event member side)
      (Gap (.inr edge) event member side)) occupied := by
  let G := geometry event
  let Rbank := G.model.bank side
  let k := Fin.last ((D).positiveContourBankLength Selection contour event)
  have genuine := K.compatibleContourGapBank_edge_ne_zero compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts Models event side
  have straight := K.compatibleContourGapBank_straightTail compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W event G side
  have nonzero : Rbank.direction ≠ 0 := straight.symm ▸ genuine k
  have index := (D).contourGapBankIndex_last Selection contour edge event
    (((D).mem_contourEdgeGapStack Selection contour edge.val event).mpr
      (((D).mem_contourSavedGapStack Selection contour edge.val event).mp member))
  have finite : Gap (.inl Child[edge]) event member side = G.model.edgePoint side k := by
    funext t
    exact congrArg (fun i => G.model.edgePoint side i t) index
  have closed := K.compatibleContourGapMark_isClosedEmbedding compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W Models
  have join := K.compatibleContourGapMark_join compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W Models edge event member side
  refine ⟨?_, ‖Rbank.direction‖, norm_pos_iff.mpr nonzero, ?_, ?_⟩
  · rw [joinedBank_range _ _ join.symm]
    exact (closed (.inl Child[edge]) event member side).isClosed_range.union
      (closed (.inr edge) event member side).isClosed_range
  · intro s
    rw [finite]
    exact (G.model.edist_joinedBank side straight Zero s).trans (by
      rw [show (Zero).val = 0 from rfl, zero_sub, abs_neg])
  · rw [finite]
    exact G.exists_model_straightJoin_normalized_chart side occupied straight genuine

/-- The actual two banks at any rim slot have oppositely occupied half-plane charts. -/
theorem compatibleContourJoinedBank_charts
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (right : Bool) :
    JoinBankChart Join[edge,i,right] right := by
  have base (side occupied : Bool) := K.compatibleContourRoofJoin_chart compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W geometry edge
      side occupied
  have gap (event : Event) (member : event ∈ Stack (.inr edge)) (side occupied : Bool) :=
    K.compatibleContourGapJoin_chart compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W geometry edge event member side occupied
  let P (side : Bool) (B : Σ j, (unitInterval → Pieces j) × (ℝ≥0 → Pieces j)) :=
    JoinBankChart (joinedBank B.2.1 B.2.2) side
  change P right Data[edge,i,right]
  cases right
  · rw [compatibleContourJoinBankData]
    split
    · exact base false false
    · exact gap _ (List.getElem_mem _) true false
  · rw [compatibleContourJoinBankData]
    split
    · exact gap _ (List.getElem_mem _) false true
    · exact base true true

end Unfoldings.ConvexRoof
