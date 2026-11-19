module

public import Unfoldings.Roof.CompatibleContourRoofJoinChart
public import Unfoldings.Roof.CompatibleContourGapStraightTail
public import Unfoldings.Roof.CompatibleContourTerminalJoinEndpoints
public import Unfoldings.Metric.JoinedBankParameters

/-! Typed joined-bank curves retain both original bank ranges and their signed charts. -/

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

local instance contourJoinBankChartMeshFintype : Fintype (T).Index :=
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

local instance contourJoinBankChartWholeFintype : Fintype W.Index := W.finiteIndex

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
local notation "TailSlot[" e "," i "]" => (Sigma.mk (Sum.inr e) i : BankStackSlot Stack)
local notation "LastSlot[" e "," i "]" => (Sigma.mk (Sum.inl Child[e]) i : BankStackSlot Stack)
local notation "Endpoint" => bankStackEndpoint Stack Pieces Base Gap

/-- Keep the original two bank curves together with their common intrinsic piece tag. -/
def compatibleContourJoinBankData
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) :
    Bool → Σ j, (unitInterval → Pieces j) × (ℝ≥0 → Pieces j)
  | true =>
    if before : i.val < (Stack (.inr edge)).length then
      let g := (Stack (.inr edge))[i.val]
      ⟨some g, Gap (.inl Child[edge]) g (List.getElem_mem before) false,
        Gap (.inr edge) g (List.getElem_mem before) false⟩
    else ⟨none, Base (.inl Child[edge]) true, Base (.inr edge) true⟩
  | false =>
    if first : i.val = 0 then
      ⟨none, Base (.inl Child[edge]) false, Base (.inr edge) false⟩
    else
      let g := (Stack (.inr edge))[i.val - 1]'(by have := i.isLt; omega)
      ⟨some g, Gap (.inl Child[edge]) g (List.getElem_mem _) true,
        Gap (.inr edge) g (List.getElem_mem _) true⟩

local notation "Data[" e "," i "," side "]" => K.compatibleContourJoinBankData compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts W geometry e i side

/-- The typed original finite curve has its literal original endpoint formula. -/
theorem compatibleContourJoinBankData_finite
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (right : Bool) (t : unitInterval) :
    let B := Data[edge,i,right]
    (⟨B.1, B.2.1 t⟩ : Total Pieces) = Endpoint right LastSlot[edge,i] t := by
  cases right
  · change _ = bankStackLeft Pieces Stack Base Gap LastSlot[edge,i] t
    rw [compatibleContourJoinBankData]
    unfold bankStackLeft
    by_cases h : i.val = 0
    · rw [dite_eq_left h, dite_eq_left (show (LastSlot[edge,i]).2.val = 0 from h)]
    · rw [dite_eq_right h, dite_eq_right (show (LastSlot[edge,i]).2.val ≠ 0 from h)]
      rfl
  · change _ = bankStackRight Pieces Stack Base Gap LastSlot[edge,i] t
    rw [compatibleContourJoinBankData]
    unfold bankStackRight
    by_cases h : i.val < (Stack (.inr edge)).length
    · rw [dite_eq_left h, dite_eq_left (show (LastSlot[edge,i]).2.val <
          (Stack (LastSlot[edge,i]).1).length from h)]
      rfl
    · rw [dite_eq_right h, dite_eq_right (show ¬ (LastSlot[edge,i]).2.val <
          (Stack (LastSlot[edge,i]).1).length from h)]

/-- The typed whole tail has its literal original endpoint formula. -/
theorem compatibleContourJoinBankData_tail
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (right : Bool) (t : ℝ≥0) :
    let B := Data[edge,i,right]
    (⟨B.1, B.2.2 t⟩ : Total Pieces) = Endpoint right TailSlot[edge,i] t := by
  cases right
  · change _ = bankStackLeft Pieces Stack Base Gap TailSlot[edge,i] t
    rw [compatibleContourJoinBankData]
    unfold bankStackLeft
    by_cases h : i.val = 0
    · rw [dite_eq_left h, dite_eq_left (show (TailSlot[edge,i]).2.val = 0 from h)]
    · rw [dite_eq_right h, dite_eq_right (show (TailSlot[edge,i]).2.val ≠ 0 from h)]
  · change _ = bankStackRight Pieces Stack Base Gap TailSlot[edge,i] t
    rw [compatibleContourJoinBankData]
    unfold bankStackRight
    by_cases h : i.val < (Stack (.inr edge)).length
    · rw [dite_eq_left h, dite_eq_left (show (TailSlot[edge,i]).2.val <
          (Stack (TailSlot[edge,i]).1).length from h)]
    · rw [dite_eq_right h, dite_eq_right (show ¬ (TailSlot[edge,i]).2.val <
          (Stack (TailSlot[edge,i]).1).length from h)]

abbrev compatibleContourJoinedBank
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (right : Bool) :
    BankJoinTime → Pieces (Data[edge,i,right]).1 :=
  joinedBank (Data[edge,i,right]).2.1 (Data[edge,i,right]).2.2

local notation "Join[" e "," i "," right "]" =>
  K.compatibleContourJoinedBank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W geometry e i right

/-- The two closed original intervals meet at the same mark in their common piece. -/
theorem compatibleContourJoinBankData_at_join
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (right : Bool) :
    let B := Data[edge,i,right]
    B.2.1 1 = B.2.2 0 := by
  have finite := K.compatibleContourJoinBankData_finite compact nonempty R no_boundary level higher
    M positive inner_disk beta acute contour starts W geometry edge i right 1
  have tail := K.compatibleContourJoinBankData_tail compact nonempty R no_boundary level higher
    M positive inner_disk beta acute contour starts W geometry edge i right 0
  have equal := K.compatibleContourTerminalJoin_endpoint compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W Models edge i right
  exact eq_of_heq (Sigma.mk.inj (finite.trans (equal.trans tail.symm))).2

/-- The signed coordinate retains the tagged finite values. -/
theorem compatibleContourJoinedBank_finite
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (right : Bool) (t : unitInterval) :
    (⟨(Data[edge,i,right]).1, Join[edge,i,right] (bankJoinFiniteTime t)⟩ : Total Pieces) =
      Endpoint right LastSlot[edge,i] t := by
  let B := Data[edge,i,right]
  have join := K.compatibleContourJoinBankData_at_join compact nonempty R no_boundary level higher
    M positive inner_disk beta acute contour starts W geometry edge i right
  exact (congrArg (Sigma.mk B.1) (joinedBank_finite B.2.1 B.2.2 join t)).trans
    (K.compatibleContourJoinBankData_finite compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W geometry edge i right t)

/-- The signed coordinate retains the tagged tail values. -/
theorem compatibleContourJoinedBank_tail
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (right : Bool) (t : ℝ≥0) :
    (⟨(Data[edge,i,right]).1, Join[edge,i,right] (bankJoinTailTime t)⟩ : Total Pieces) =
      Endpoint right TailSlot[edge,i] t := by
  let B := Data[edge,i,right]
  exact (congrArg (Sigma.mk B.1) (joinedBank_tail B.2.1 B.2.2 t)).trans
    (K.compatibleContourJoinBankData_tail compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W geometry edge i right t)

end Unfoldings.ConvexRoof
