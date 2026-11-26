module

public import Unfoldings.FewestNets.ThreeExitGraftTerminalJoinClasses
public import Unfoldings.FewestNets.ThreeExitGraftMarkMetrics
public import Unfoldings.Roof.CompatibleContourJoinedBankCharts
public import Unfoldings.Geometry.StraightGapJoinBank

/-! A single signed metric bank crosses each actual three-exit exit join. -/

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

local instance graftJoinChartsIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams Left Right

local notation "Exit" => TriangleComplex.ContourTerminalEdge D Selection
local notation "Point" => MetricGluing.point Pieces Banks
local notation "LeftCurve" => bankStackLeftCurve Stack Pieces Base Gap
local notation "RightCurve" => bankStackRightCurve Stack Pieces Base Gap


local notation "Edge" => Exit
local notation "Child[" e "]" => (Subtype.mk (Subtype.val e) (And.left (Subtype.property e)))
local notation "TailSlot[" e "," i "]" => (Sigma.mk (Sum.inr e) i : BankStackSlot Stack)
local notation "LastSlot[" e "," i "]" => (Sigma.mk (Sum.inl Child[e]) i : BankStackSlot Stack)
local notation "Endpoint" => bankStackEndpoint Stack Pieces Base Gap

/-- Keep the original two bank curves together with their common intrinsic piece tag. -/
def contourGraftJoinBankData
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

local notation "Data[" e "," i "," side "]" => L.contourGraftJoinBankData S e i side

/-- The typed original finite curve has its literal original endpoint formula. -/
theorem contourGraftJoinBankData_finite
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (right : Bool) (t : unitInterval) :
    let B := Data[edge,i,right]
    (⟨B.1, B.2.1 t⟩ : Total Pieces) = Endpoint right LastSlot[edge,i] t := by
  cases right
  · change _ = bankStackLeft Pieces Stack Base Gap LastSlot[edge,i] t
    rw [contourGraftJoinBankData]
    unfold bankStackLeft
    by_cases h : i.val = 0
    · rw [dite_eq_left h, dite_eq_left (show (LastSlot[edge,i]).2.val = 0 from h)]
    · rw [dite_eq_right h, dite_eq_right (show (LastSlot[edge,i]).2.val ≠ 0 from h)]
      rfl
  · change _ = bankStackRight Pieces Stack Base Gap LastSlot[edge,i] t
    rw [contourGraftJoinBankData]
    unfold bankStackRight
    by_cases h : i.val < (Stack (.inr edge)).length
    · rw [dite_eq_left h, dite_eq_left (show (LastSlot[edge,i]).2.val <
          (Stack (LastSlot[edge,i]).1).length from h)]
      rfl
    · rw [dite_eq_right h, dite_eq_right (show ¬ (LastSlot[edge,i]).2.val <
          (Stack (LastSlot[edge,i]).1).length from h)]

/-- The typed whole tail has its literal original endpoint formula. -/
theorem contourGraftJoinBankData_tail
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (right : Bool) (t : ℝ≥0) :
    let B := Data[edge,i,right]
    (⟨B.1, B.2.2 t⟩ : Total Pieces) = Endpoint right TailSlot[edge,i] t := by
  cases right
  · change _ = bankStackLeft Pieces Stack Base Gap TailSlot[edge,i] t
    rw [contourGraftJoinBankData]
    unfold bankStackLeft
    by_cases h : i.val = 0
    · rw [dite_eq_left h, dite_eq_left (show (TailSlot[edge,i]).2.val = 0 from h)]
    · rw [dite_eq_right h, dite_eq_right (show (TailSlot[edge,i]).2.val ≠ 0 from h)]
  · change _ = bankStackRight Pieces Stack Base Gap TailSlot[edge,i] t
    rw [contourGraftJoinBankData]
    unfold bankStackRight
    by_cases h : i.val < (Stack (.inr edge)).length
    · rw [dite_eq_left h, dite_eq_left (show (TailSlot[edge,i]).2.val <
          (Stack (TailSlot[edge,i]).1).length from h)]
    · rw [dite_eq_right h, dite_eq_right (show ¬ (TailSlot[edge,i]).2.val <
          (Stack (TailSlot[edge,i]).1).length from h)]

abbrev contourGraftJoinedBank
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (right : Bool) :
    BankJoinTime → Pieces (Data[edge,i,right]).1 :=
  joinedBank (Data[edge,i,right]).2.1 (Data[edge,i,right]).2.2

local notation "Join[" e "," i "," right "]" =>
  L.contourGraftJoinedBank S e i right

/-- The two closed original intervals meet at the same mark in their common piece. -/
theorem contourGraftJoinBankData_at_join
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (right : Bool) :
    let B := Data[edge,i,right]
    B.2.1 1 = B.2.2 0 := by
  have finite := L.contourGraftJoinBankData_finite S edge i right 1
  have tail := L.contourGraftJoinBankData_tail S edge i right 0
  have equal := L.contourGraft_terminalJoin_endpoint S edge i right
  exact eq_of_heq (Sigma.mk.inj (finite.trans (equal.trans tail.symm))).2

/-- The signed coordinate retains the tagged finite values. -/
theorem contourGraftJoinedBank_finite
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (right : Bool) (t : unitInterval) :
    (⟨(Data[edge,i,right]).1, Join[edge,i,right] (bankJoinFiniteTime t)⟩ : Total Pieces) =
      Endpoint right LastSlot[edge,i] t := by
  let B := Data[edge,i,right]
  have join := L.contourGraftJoinBankData_at_join S edge i right
  exact (congrArg (Sigma.mk B.1) (joinedBank_finite B.2.1 B.2.2 join t)).trans
    (L.contourGraftJoinBankData_finite S edge i right t)

/-- The signed coordinate retains the tagged tail values. -/
theorem contourGraftJoinedBank_tail
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (right : Bool) (t : ℝ≥0) :
    (⟨(Data[edge,i,right]).1, Join[edge,i,right] (bankJoinTailTime t)⟩ : Total Pieces) =
      Endpoint right TailSlot[edge,i] t := by
  let B := Data[edge,i,right]
  exact (congrArg (Sigma.mk B.1) (joinedBank_tail B.2.1 B.2.2 t)).trans
    (L.contourGraftJoinBankData_tail S edge i right t)


local notation "Zero" => (Subtype.mk (0 : ℝ) (by norm_num) : BankJoinTime)


private theorem gapJoin_chart (edge : Edge) (event : Event)
    (member : event ∈ Stack (.inr edge)) (side occupied : Bool) :
    JoinBankChart (joinedBank (Gap (.inl Child[edge]) event member side)
      (Gap (.inr edge) event member side)) occupied := by
  let gap := S.gaps event
  let Rbank := gap.model.bank (!side)
  let k := Fin.last ((D).positiveContourBankLength Selection S.contour event)
  have genuine (j) : Rbank.chain.edge j ≠ 0 := by
    let bank := (Fcut).contourSourceRay S.contour S.starts event
    let angle := (D).interiorAngularDefect Set.univ
      ((D).positiveContourVertex Selection S.contour event)
    have nonzero : bank.chain.edge j ≠ 0 := (D).boundaryChainRoll_edge_ne_zero
      ((Fcut).contourSourceBankChain S.contour S.starts event) j
    cases side
    · change (bank.rotateSuffix 0 angle).chain.edge j ≠ 0
      rw [bank.rotateSuffix_zero_edge]
      simpa only [map_zero] using (complexRotation angle).injective.ne nonzero
    · exact nonzero
  have straight := contourGraftGap_direction_eq_last S event (!side)
  have nonzero : Rbank.direction ≠ 0 := straight.symm ▸ genuine k
  have index := (D).contourGapBankIndex_last Selection S.contour edge event
    (((D).mem_contourEdgeGapStack Selection S.contour edge.val event).mpr
      (((D).mem_contourSavedGapStack Selection S.contour edge.val event).mp member))
  have finite : Gap (.inl Child[edge]) event member side = gap.model.edgePoint (!side) k := by
    funext t
    exact congrArg (fun i => gap.model.edgePoint (!side) i t) index
  have closed := isClosedEmbedding_contourGapMark S
  have join := PotentialCutForest.contourGapMark_tail_zero Fcut S.contour S.starts
    (fun e : Event => Model[e]) edge event member side
  refine ⟨?_, ‖Rbank.direction‖, norm_pos_iff.mpr nonzero, ?_, ?_⟩
  · rw [joinedBank_range _ _ join.symm]
    exact (closed (.inl Child[edge]) event member side).isClosed_range.union
      (closed (.inr edge) event member side).isClosed_range
  · intro s
    rw [finite]
    exact (gap.model.edist_joinedBank (!side) straight Zero s).trans (by
      rw [show (Zero).val = 0 from rfl, zero_sub, abs_neg])
  · rw [finite]
    exact gap.exists_model_straightJoin_normalized_chart (!side) occupied straight genuine

private theorem baseJoin_chart (edge : Edge) (side occupied : Bool) :
    JoinBankChart (joinedBank (Base (.inl Child[edge]) side) (Base (.inr edge) side)) occupied := by
  refine ⟨?_, (L.contourTerminalContinuation S.higher S.contour S.starts edge).joined_chart side occupied⟩
  rw [joinedBank_range _ _ (L.contourBaseMark_tail_zero S edge side).symm]
  exact (L.isClosedEmbedding_contourBaseMark S (.inl Child[edge]) side).isClosed_range.union
    (L.isClosedEmbedding_contourBaseMark S (.inr edge) side).isClosed_range

/-- The actual two banks at any exit join have oppositely occupied half-plane charts. -/
theorem contourGraftJoinedBank_charts
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (right : Bool) :
    JoinBankChart Join[edge,i,right] right := by
  let P (side : Bool) (B : Σ j, (unitInterval → Pieces j) × (ℝ≥0 → Pieces j)) :=
    JoinBankChart (joinedBank B.2.1 B.2.2) side
  change P right Data[edge,i,right]
  cases right
  · rw [contourGraftJoinBankData]
    split
    · exact baseJoin_chart L S edge false false
    · exact gapJoin_chart S edge _ (List.getElem_mem _) true false
  · rw [contourGraftJoinBankData]
    split
    · exact gapJoin_chart S edge _ (List.getElem_mem _) false true
    · exact baseJoin_chart L S edge true true

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
