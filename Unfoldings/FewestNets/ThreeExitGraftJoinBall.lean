module

public import Unfoldings.FewestNets.ThreeExitGraftJoinCharts
public import Unfoldings.FewestNets.ThreeExitGraftLabels
public import Unfoldings.Metric.BankStackSeamExcision

/-! The entire three-exit graft has a planar ball at each exit join. -/

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

local instance graftJoinBallIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

local notation "Edge" => Exit
local notation "Child[" e "]" => (Subtype.mk (Subtype.val e) (And.left (Subtype.property e)))
local notation "TailSlot[" e "," i "]" => (Sigma.mk (Sum.inr e) i : BankStackSlot Stack)
local notation "LastSlot[" e "," i "]" => (Sigma.mk (Sum.inl Child[e]) i : BankStackSlot Stack)
local notation "Endpoint" => bankStackEndpoint Stack Pieces Base Gap

local notation "Data[" e "," i "," side "]" => L.contourGraftJoinBankData S e i side
local notation "Join[" e "," i "," side "]" => L.contourGraftJoinedBank S e i side
local notation "Point[" e "," i "," side "," s "]" =>
  (Sigma.mk (Sigma.fst Data[e,i,side]) (Join[e,i,side] s) : Total Pieces)
local notation "Keep[" e "," i "]" => ({LastSlot[e,i],TailSlot[e,i]} : Set (BankStackSlot Stack))
local notation "LeftAt" => bankStackLeft Pieces Stack Base Gap
local notation "RightAt" => bankStackRight Pieces Stack Base Gap
local notation "Selected[" e "," i "]" => bankStackSelectedSeams Pieces Stack Base Gap Keep[e,i]
local notation "Pair[" e "," i "]" => bankPairGlue Pieces Join[e,i,false] Join[e,i,true]
local notation "Zero" => (Subtype.mk (0 : ℝ) (by norm_num) : BankJoinTime)

/-- Each signed seam parameter names one pair on one original slot. Both tags are exact. -/
theorem contourGraftJoinedBank_originalSlot
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (s : BankJoinTime) :
    ∃ slot : Keep[edge,i], ∃ t : Param slot.val.1,
      ∀ side, Point[edge,i,side,s] = Endpoint side slot.val t := by
  by_cases before : s.val < 0
  · have lower : -1 ≤ s.val := s.property
    let t : unitInterval := ⟨1 + s.val, by linarith, by linarith⟩
    have time : bankJoinFiniteTime t = s := by
      apply Subtype.ext
      change (1 + s.val) - 1 = s.val
      ring
    refine ⟨⟨LastSlot[edge,i], Set.mem_insert _ _⟩, t, fun side => ?_⟩
    rw [← time]
    exact L.contourGraftJoinedBank_finite S edge i side t
  · let t : ℝ≥0 := ⟨s.val, le_of_not_gt before⟩
    refine ⟨⟨TailSlot[edge,i], Set.mem_insert_of_mem _ (Set.mem_singleton _)⟩, t, fun side => ?_⟩
    exact L.contourGraftJoinedBank_tail S edge i side t

/-- The two selected original slot relations are exactly the joined signed relation. -/
theorem contourGraftJoinedBank_seams
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (x y : Total Pieces) :
    Pair[edge,i] x y ↔ Selected[edge,i] x y := by
  constructor
  · rintro ⟨s, hx, hy⟩
    obtain ⟨slot, t, eq⟩ := L.contourGraftJoinedBank_originalSlot S edge i s
    exact ⟨slot, t, hx.trans (eq false), hy.trans (eq true)⟩
  · rintro ⟨⟨slot, keep⟩, t, hx, hy⟩
    rcases Set.mem_insert_iff.mp keep with hf | ht
    · subst slot
      let f := L.contourGraftJoinedBank_finite S edge i
      exact ⟨bankJoinFiniteTime t, hx.trans (f false t).symm, hy.trans (f true t).symm⟩
    · have eq := Set.mem_singleton_iff.mp ht
      subst slot
      let f := L.contourGraftJoinedBank_tail S edge i
      exact ⟨bankJoinTailTime t, hx.trans (f false t).symm, hy.trans (f true t).symm⟩

private theorem contourGraftJoinedBank_speed_eq
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1))
    {a b : ℝ} (apos : 0 < a) (bpos : 0 < b)
    (left : ∀ s, edist (Join[edge,i,false] Zero) (Join[edge,i,false] s) =
      ENNReal.ofReal (|s.val| * a))
    (right : ∀ s, edist (Join[edge,i,true] Zero) (Join[edge,i,true] s) =
      ENNReal.ofReal (|s.val| * b)) : a = b := by
  let slot := TailSlot[edge,i]
  let (a : Attachment) : MetricSpace (Param a) := contourAttachmentMetric S a
  have rep (side : Bool) (t : ℝ≥0) :=
    L.contourGraftJoinedBank_tail S edge i side t
  have bm := L.edist_contourBaseMark_sides S
  have gm := L.edist_contourGapMark_eq_base S
  have distance : faceCost Pieces (LeftAt slot 0) (LeftAt slot 1) =
      faceCost Pieces (RightAt slot 0) (RightAt slot 1) := by
    have left_label := congrArg₂ (faceCost Pieces)
      (bankStackLeft_curve Stack Pieces Base Gap slot 0)
      (bankStackLeft_curve Stack Pieces Base Gap slot 1)
    have right_label := congrArg₂ (faceCost Pieces)
      (bankStackRight_curve Stack Pieces Base Gap slot 0)
      (bankStackRight_curve Stack Pieces Base Gap slot 1)
    exact left_label.trans ((faceCost_same_tag _ _ _ _).trans
      ((bankStackCurves_same_metric Stack Pieces Base Gap bm gm slot 0 1).trans
        ((faceCost_same_tag _ _ _ _).symm.trans right_label.symm)))
  have same : edist (Join[edge,i,false] Zero) (Join[edge,i,false] (bankJoinTailTime 1)) =
      edist (Join[edge,i,true] Zero) (Join[edge,i,true] (bankJoinTailTime 1)) := by
    calc
      _ = faceCost Pieces Point[edge,i,false,Zero] Point[edge,i,false,bankJoinTailTime 1] :=
        (faceCost_same_tag _ _ _ _).symm
      _ = faceCost Pieces (LeftAt slot 0) (LeftAt slot 1) := by
        exact congrArg₂ (faceCost Pieces) (rep false 0) (rep false 1)
      _ = faceCost Pieces (RightAt slot 0) (RightAt slot 1) := distance
      _ = faceCost Pieces Point[edge,i,true,Zero] Point[edge,i,true,bankJoinTailTime 1] := by
        exact congrArg₂ (faceCost Pieces) (rep true 0).symm (rep true 1).symm
      _ = _ := faceCost_same_tag _ _ _ _
  have lengths := (left (bankJoinTailTime 1)).symm.trans
    (same.trans (right (bankJoinTailTime 1)))
  change ENNReal.ofReal (|(1 : ℝ)| * a) = ENNReal.ofReal (|(1 : ℝ)| * b) at lengths
  rw [abs_one, one_mul, one_mul] at lengths
  exact (ENNReal.ofReal_eq_ofReal_iff apos.le bpos.le).mp lengths

/-- The exact signed bank relation has a full planar ball at its join. -/
theorem contourGraft_terminalJoin_pair_planarBall
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) :
    HasMetricBallChart ℂ (point Pieces Pair[edge,i] Point[edge,i,false,Zero]) := by
  obtain ⟨lc, a, apos, lm, r₁, ⟨leftChart⟩⟩ := L.contourGraftJoinedBank_charts S edge i false
  obtain ⟨rc, b, bpos, rm, r₂, ⟨B⟩⟩ := L.contourGraftJoinedBank_charts S edge i true
  have speed := L.contourGraftJoinedBank_speed_eq S edge i apos bpos lm rm
  subst b
  have available : (Zero).val ∈ interior (Set.range (Subtype.val : BankJoinTime → ℝ)) := by
    rw [Subtype.range_coe]
    change (0 : ℝ) ∈ interior (Set.Ici (-1 : ℝ))
    rw [interior_Ici]
    exact neg_one_lt_zero
  have away (side : Bool) (s : BankJoinTime) :
      Point[edge,i,side,Zero] ≠ Point[edge,i,!side,s] := by
    intro equal
    obtain ⟨slot, t, labels⟩ := L.contourGraftJoinedBank_originalSlot S edge i s
    have at_zero := L.contourGraftJoinedBank_tail S edge i side 0
    have h : Endpoint (!side) slot.val t = Endpoint side TailSlot[edge,i] 0 :=
      (labels (!side)).symm.trans (equal.symm.trans at_zero)
    have named := L.contourGraft_terminalJoin_endpoint_eq S edge i side
      (!side) slot.val t h
    exact (Bool.not_eq_self side).mp named.1
  refine bankPair_planarBall_of_charts Pieces Join[edge,i,false] Join[edge,i,true]
    Zero Subtype.val (R₁ := r₁) (R₂ := r₂) ?_ ?_ apos available ?_ ?_ lc rc
      (away true) (away false)
  · simpa only [sub_zero] using leftChart
  · simpa only [sub_zero] using B
  · simpa only [sub_zero] using lm
  · simpa only [sub_zero] using rm

/-- The actual full graft has a whole planar ball at every original terminal join. -/
theorem contourGraft_terminalJoin_planarBall
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) :
    HasMetricBallChart ℂ (point Pieces Banks (LeftAt TailSlot[edge,i] 0)) := by
  let seam := L.contourGraftJoinedBank_seams S edge i
  let E := changeSeamsIsometryEquiv Pieces (R := Pair[edge,i]) (S := Selected[edge,i])
    (fun a b h => point_eq_of_glue Pieces ((seam a b).mp h))
    (fun a b h => point_eq_of_glue Pieces ((seam a b).mpr h))
  let x := Point[edge,i,false,Zero]
  let y := LeftAt TailSlot[edge,i] 0
  have center : E (point Pieces Pair[edge,i] x) = point Pieces Selected[edge,i] y :=
    congrArg (point Pieces Selected[edge,i])
      (L.contourGraftJoinedBank_tail S edge i false 0)
  have joined := L.contourGraft_terminalJoin_pair_planarBall S edge i
  have plane : HasMetricBallChart ℂ (point Pieces Selected[edge,i] y) := by
    rw [← center]
    exact joined.isometryEquiv E
  let (a : Attachment) : TopologicalSpace (Param a) := (contourAttachmentMetric S a).toUniformSpace.toTopologicalSpace
  let first : Σ slot : BankStackSlot Stack, Param slot.1 := ⟨TailSlot[edge,i], 0⟩
  let second : Σ slot : BankStackSlot Stack, Param slot.1 := ⟨LastSlot[edge,i], 1⟩
  obtain ⟨ε, εpos, cover⟩ := L.contourGraft_piece_ball_cover S y
  obtain ⟨δ, δpos, slots⟩ := bankStack_exists_near_two_slots Stack Pieces Base Gap first second
    (fun z => (L.contourGraft_terminalJoin_eqvGen_pair S edge i z).mp)
    (fun side other p => L.contourGraft_terminalJoin_endpoint_eq S
      edge i side other p.1 p.2)
    (L.isClosedEmbedding_contourBaseMark S)
    (isClosedEmbedding_contourGapMark S)
    εpos cover
  obtain ⟨r, rpos, A, exact_center⟩ :=
    bankStack_exists_selected_forgetChart Pieces Stack Base Gap Keep[edge,i] y δpos
      (fun slot t near => by
        rcases slots slot t near with first | second
        · exact first.symm ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _)
        · exact second.symm ▸ Set.mem_insert _ _)
  exact plane.of_centered_ball_equiv rpos A exact_center

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
