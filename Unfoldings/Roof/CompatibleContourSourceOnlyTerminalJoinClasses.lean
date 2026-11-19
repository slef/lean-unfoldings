module

public import Unfoldings.Roof.CompatibleContourSourceOnlyTerminalJoinMarks
public import Unfoldings.Roof.CompatibleContourTerminalJoinEndpoints
public import Unfoldings.Metric.BankStackAdjacentGaps

/-! Exact original seam classes at the finite-to-infinite source-only joins. -/

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

local instance sourceOnlyTerminalJoinEndpointMeshFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut

local notation "BankAt[" q "," h "," e "]" =>
  K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e
local notation "OpenedAt[" q "," h "," e "]" =>
  K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e

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

local instance sourceOnlyTerminalJoinEndpointWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Pieces" => polygonalBankStackPiece W.Cut
  (fun e : TriangleComplex.PositiveContourSource D Selection contour => BankGapModel.region (models e))
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W
local notation "Gap" => K.compatibleContourSourceOnlyGapMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts models

local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute

local notation "Edge" => TriangleComplex.ContourTerminalEdge D Selection


local notation "Child[" e "]" => (Subtype.mk (Subtype.val e) (And.left (Subtype.property e)))
local notation "LastPair[" e "]" => (Sigma.mk (Sum.inl Child[e]) 1 : Σ b : Attachment, ParamAt b)
local notation "TailPair[" e "]" => (Sigma.mk (Sum.inr e) 0 : Σ b : Attachment, ParamAt b)


local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "TailSlot[" e "," i "]" => (Sigma.mk (Sum.inr e) i : BankStackSlot Stack)
local notation "LastSlot[" e "," i "]" => (Sigma.mk (Sum.inl Child[e]) i : BankStackSlot Stack)
local notation "Endpoint" => bankStackEndpoint Stack Pieces Base Gap
local notation "Address" => bankStackEndpointAddress (Parameter := ParamAt) Stack

/-- Either endpoint of the actual terminal slot is also the endpoint of the same
consecutive finite slot. The roof tags and original gap tags are retained. -/
theorem compatibleContourSourceOnlyTerminalJoin_endpoint
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (side : Bool) :
    Endpoint side LastSlot[edge,i] 1 = Endpoint side TailSlot[edge,i] 0 := by
  have base (side : Bool) := K.compatibleContourTerminalMark_zero compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W edge side
  have gap (g : (D).PositiveContourSource Selection contour) (member : g ∈ Stack (.inr edge))
      (side : Bool) := K.compatibleContourSourceOnlyGapMark_join compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts models edge g member side
  cases side
  · change bankStackLeft Pieces Stack Base Gap LastSlot[edge,i] 1 =
      bankStackLeft Pieces Stack Base Gap TailSlot[edge,i] 0
    unfold bankStackLeft
    split_ifs
    · exact congrArg (Sigma.mk none) (base false).symm
    · exact congrArg (Sigma.mk _) (gap _ (List.getElem_mem _) true).symm
  · change bankStackRight Pieces Stack Base Gap LastSlot[edge,i] 1 =
      bankStackRight Pieces Stack Base Gap TailSlot[edge,i] 0
    unfold bankStackRight
    by_cases before : i.val < (Stack (.inr edge)).length
    · rw [dite_eq_left (show (LastSlot[edge,i]).2.val < (Stack (LastSlot[edge,i]).1).length
            from before),
          dite_eq_left (show (TailSlot[edge,i]).2.val < (Stack (TailSlot[edge,i]).1).length
            from before)]
      exact congrArg (Sigma.mk _) (gap _ (List.getElem_mem _) false).symm
    · rw [dite_eq_right (show ¬ (LastSlot[edge,i]).2.val < (Stack (LastSlot[edge,i]).1).length
            from before),
          dite_eq_right (show ¬ (TailSlot[edge,i]).2.val < (Stack (TailSlot[edge,i]).1).length
            from before)]
      exact congrArg (Sigma.mk none) (base true).symm

/-- Equality with an original join mark recovers its endpoint side and its finite or
terminal slot address. -/
theorem compatibleContourSourceOnlyTerminalJoin_endpoint_eq
    (geometry : ∀ event : (D).PositiveContourSource Selection contour,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (side other_side : Bool)
    (other : BankStackSlot Stack) (s : ParamAt other.1)
    (equal : Endpoint other_side other s = Endpoint side TailSlot[edge,i] 0) :
    other_side = side ∧
      ((⟨other, s⟩ : Σ slot : BankStackSlot Stack, ParamAt slot.1) = ⟨TailSlot[edge,i], 0⟩ ∨
        (⟨other, s⟩ : Σ slot : BankStackSlot Stack, ParamAt slot.1) = ⟨LastSlot[edge,i], 1⟩) := by
  let P (p : Σ b, ParamAt b) := p = TailPair[edge] ∨ p = LastPair[edge]
  have covered : BankStackMarkParametersAt Stack Pieces Base Gap (.inr edge) 0 P := by
    constructor
    · intro side' f flag t h
      exact K.compatibleContourOriginalBankMark_eq_terminal_join compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W edge f side' flag t h
    · intro event member side' f other_member flag t h
      exact K.compatibleContourSourceOnlyGapMark_eq_terminal_join compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts models event (geometry event)
        edge f member other_member side' flag t h
  let b := Address other_side other s
  let a := Address side TailSlot[edge,i] 0
  obtain ⟨piece, flag, choice⟩ := bankStackEndpoint_tags_of_point_eq Stack Pieces Base Gap side
    other_side TailSlot[edge,i] other 0 s covered equal
  have assemble (p : Σ b, ParamAt b) (same : (⟨b.1, b.2.2.2⟩ : Σ b, ParamAt b) = p) :
      b = ⟨p.1, a.2.1, a.2.2.1, p.2⟩ := by
    change b.2.1 = a.2.1 at piece
    change b.2.2.1 = a.2.2.1 at flag
    calc
      b = ⟨b.1, a.2.1, a.2.2.1, b.2.2.2⟩ := by rw [← piece, ← flag]
      _ = _ := congrArg (fun q : Σ b, ParamAt b =>
        (⟨q.1, a.2.1, a.2.2.1, q.2⟩ : BankStackAddress (G := _) (Parameter := _))) same
  have nodup := K.compatibleContourBankStack_nodup compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour
  have key := bankStackEndpointAddress_parameter Stack other_side other s
  rcases choice with tail | last
  · have addresses : b = a := by
      have a_key := bankStackEndpointAddress_parameter (Parameter := ParamAt) Stack side
        TailSlot[edge,i] (0 : ℝ≥0)
      change (⟨a.1, a.2.2.2⟩ : Σ b, ParamAt b) = TailPair[edge] at a_key
      exact assemble ⟨a.1, a.2.2.2⟩ (key.trans (tail.trans a_key.symm))
    have eq := bankStackEndpointAddress_injective Stack nodup
      (a₁ := (other_side, ⟨other, s⟩)) (a₂ := (side, ⟨TailSlot[edge,i], 0⟩)) addresses
    exact ⟨congrArg Prod.fst eq, Or.inl (congrArg Prod.snd eq)⟩
  · have addresses : b = Address side LastSlot[edge,i] 1 :=
      (assemble LastPair[edge] (key.trans last)).trans
        (K.compatibleContourTerminalJoin_address_shift compact nonempty R no_boundary level
          higher M positive inner_disk beta acute contour edge i side).symm
    have eq := bankStackEndpointAddress_injective Stack nodup
      (a₁ := (other_side, ⟨other, s⟩)) (a₂ := (side, ⟨LastSlot[edge,i], 1⟩)) addresses
    exact ⟨congrArg Prod.fst eq, Or.inr (congrArg Prod.snd eq)⟩

local notation "LeftAt" => bankStackLeft Pieces Stack Base Gap
local notation "RightAt" => bankStackRight Pieces Stack Base Gap
local notation "Banks" => bankSeams LeftAt RightAt

/-- The two genuine copies and the two original parameter names exhaust the exact joined class. -/
theorem compatibleContourSourceOnlyTerminalJoin_eqvGen_pair
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (x : Total Pieces) :
    Relation.EqvGen Banks (LeftAt TailSlot[edge,i] 0) x ↔
      x = LeftAt TailSlot[edge,i] 0 ∨ x = RightAt TailSlot[edge,i] 0 := by
  let first : Σ slot : BankStackSlot Stack, ParamAt slot.1 := ⟨TailSlot[edge,i], 0⟩
  let second : Σ slot : BankStackSlot Stack, ParamAt slot.1 := ⟨LastSlot[edge,i], 1⟩
  exact bankStack_eqvGen_pair_of_two_slot_times Stack Pieces Base Gap first second
    (fun side => (K.compatibleContourSourceOnlyTerminalJoin_endpoint compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W models
      edge i side).symm)
    (fun side other p => K.compatibleContourSourceOnlyTerminalJoin_endpoint_eq compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W models geometry
      edge i side other p.1 p.2) x

end Unfoldings.ConvexRoof
