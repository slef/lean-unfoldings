module

public import Unfoldings.Roof.CompatibleContourSourceOnlyRoofVertexBall
public import Unfoldings.Roof.CompatibleContourSourceOnlyUnmarkedBall
public import Unfoldings.Roof.CompatibleContourSourceOnlyGapAddressCoverage

/-! At every point of every named source-only graft seam there is a planar ball. -/

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

local instance sourceOnlyBankSlotBallIndexFintype : Fintype (T).Index :=
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
      (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance sourceOnlyBankSlotBallWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "models" => (fun event : Event => OrientedBankGap.model (geometry event))
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
local notation "FiniteBank[" v "," h "]" => (Sum.inl (Subtype.mk v h) : Attachment)
local notation "Addr" => MetricGluing.BankStackAddress (G := Event) (Parameter := ParamAt)
local notation "Named" => MetricGluing.bankStackEndpointAddress (Parameter := ParamAt) Stack
local notation "Mark" => MetricGluing.bankStackAddressPoint Stack Pieces Base Gap
local notation "Valid" => MetricGluing.BankStackAddressValid Stack
local notation "EndAt" => MetricGluing.bankStackEndpoint Stack Pieces Base Gap
local notation "L" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Rgt" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams L Rgt
local notation "Time" => (Σ s : MetricGluing.BankStackSlot Stack, ParamAt (Sigma.fst s))

local notation "BankAt[" e "]" => K.compatibleContourSourceBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "MovedAt[" e "]" => K.compatibleContourSourceOnlyBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e


local notation "Edge" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Interval[" v "," h "]" => TriangleComplex.contourParentInterval
  D Selection contour (PotentialCutForest.boundary_roots Fcut) starts v h
local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W
local notation "Retain" => PotentialCutForest.retain Fcut
local notation "SourceOf[" e "]" => TriangleComplex.positiveContourVertex D Selection contour e
local notation "RoofPoint[" j "]" => (Sigma.mk none (Map
  (TriangleComplex.vertexPoint D Retain (TriangleComplex.boundaryEndVertex D Retain
    (PairedInvolutions.System.Chain.point (TriangleComplex.BoundaryContour.cycle contour) j)))) :
      MetricGluing.Total Pieces)

local notation "Point" => MetricGluing.point Pieces Banks
local notation "LengthAt[" e "]" => TriangleComplex.positiveContourBankLength D Selection contour e
local notation "Terminal" => TriangleComplex.ContourTerminalEdge D Selection

local notation "Visit[" j "]" => TriangleComplex.contourOriginalVertex D Selection contour j

set_option maxHeartbeats 1550000 in
-- The full slot family has different parameter types on finite banks and infinite tails.
/-- The actual graft has a whole planar ball on every original seam slot,
with both endpoints of every finite bank and the join to every true tail. -/
theorem compatibleContourSourceOnlyBankSlot_planarBall
    (ends : Visit[Fin.last contour.length] ∈ (Fcut).parents.roots)
    (strict : ∀ (e : Event) (k : Fin LengthAt[e]), let B := BankAt[e]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ))
    (slot : MetricGluing.BankStackSlot Stack) (t : ParamAt slot.1) :
    HasMetricBallChart ℂ (Point (L slot t)) := by
  obtain ⟨b, i⟩ := slot
  cases b with
  | inr edge =>
    change ℝ≥0 at t
    by_cases at_zero : t = 0
    · subst t
      exact K.compatibleContourSourceOnlyTerminalJoin_planarBall compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts W geometry edge i
    · exact K.compatibleContourSourceOnlySmoothSeam_planarBall compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts W geometry ⟨.inr edge, i⟩ t
        (lt_of_le_of_ne zero_le (Ne.symm at_zero))
  | inl edge =>
    change unitInterval at t
    by_cases at_zero : t = 0
    · subst t
      have chart := K.compatibleContourSourceOnly_outgoingVertex_planarBall compact nonempty R
        no_boundary level higher M positive inner_disk beta acute contour starts W geometry ends
        edge strict i
      have joined : Point (L ⟨.inl edge, i⟩ 0) = Point (Rgt ⟨.inl edge, i⟩ 0) :=
        MetricGluing.point_eq_of_glue Pieces (glue := Banks) ⟨⟨.inl edge, i⟩, 0, rfl, rfl⟩
      exact Eq.mpr (congrArg (HasMetricBallChart ℂ) joined) chart
    by_cases at_one : t = 1
    · subst t
      by_cases root : (Fcut).parents.parent edge.val ∈ (Fcut).parents.roots
      · let terminal : (D).ContourTerminalEdge Selection := ⟨edge.val, edge.property, root⟩
        exact K.compatibleContourSourceOnlyTerminalFinite_planarBall compact nonempty R no_boundary
          level higher M positive inner_disk beta acute contour starts W geometry terminal i
      by_cases empty : Stack (.inl edge) = []
      · exact K.compatibleContourSourceOnlyFiniteEnd_empty_planarBall compact nonempty R no_boundary
          level higher M positive inner_disk beta acute contour starts W geometry ends strict edge
          root empty i
      · exact K.compatibleContourSourceOnlyFiniteEnd_nonempty_planarBall compact nonempty R
          no_boundary level higher M positive inner_disk beta acute contour starts W geometry ends
          edge root empty strict i
    have above : (0 : ℝ) < t.val := lt_of_le_of_ne t.property.1
      (fun h => at_zero (Subtype.ext h.symm))
    have below : t.val < (1 : ℝ) := lt_of_le_of_ne t.property.2
      (fun h => at_one (Subtype.ext h))
    exact K.compatibleContourSourceOnlySmoothSeam_planarBall compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W geometry ⟨.inl edge, i⟩ t
      ⟨above, below⟩

include W in
/-- Every valid original bank address is centered in the corresponding whole graft ball. -/
theorem compatibleContourSourceOnlyBankAddress_planarBall
    (ends : Visit[Fin.last contour.length] ∈ (Fcut).parents.roots)
    (strict : ∀ (e : Event) (k : Fin LengthAt[e]), let B := BankAt[e]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ))
    (addr : Addr) (valid : Valid addr) :
    HasMetricBallChart ℂ (Point (Mark addr valid)) := by
  obtain ⟨side, slot, t, named⟩ := MetricGluing.exists_bankStackEndpointAddress_eq Stack addr valid
  have exact_mark : EndAt side slot t = Mark addr valid := by
    let P (a : Addr) := ∀ h : Valid a, EndAt side slot t = Mark a h
    have h : P (Named side slot t) := fun _ =>
      (MetricGluing.bankStackAddressPoint_endpoint Stack Pieces Base Gap side slot t).symm
    exact (named ▸ h : P addr) valid
  have chart := K.compatibleContourSourceOnlyBankSlot_planarBall compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W geometry ends strict slot t
  have same : Point (L slot t) = Point (Mark addr valid) := by
    cases side
    · exact congrArg Point exact_mark
    · exact (MetricGluing.point_eq_of_glue Pieces (glue := Banks) ⟨slot, t, rfl, rfl⟩).trans
        (congrArg Point exact_mark)
  exact Eq.mp (congrArg (HasMetricBallChart ℂ) same) chart

end Unfoldings.ConvexRoof
