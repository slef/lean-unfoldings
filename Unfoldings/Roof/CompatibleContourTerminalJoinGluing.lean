module

public import Unfoldings.Roof.CompatibleContourJoinedBankCharts
public import Unfoldings.Roof.CompatibleContourTerminalJoinExcision
public import Unfoldings.Metric.FiniteBankHalfPlaneGluing
public import Unfoldings.Metric.LocalBallRegularity

/-! The actual two slots at a rim join form a single signed bank-pair gluing. -/

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

local instance contourTerminalJoinGluingMeshFintype : Fintype (T).Index :=
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

local instance contourTerminalJoinGluingWholeFintype : Fintype W.Index := W.finiteIndex

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


local notation "Data[" e "," i "," side "]" => K.compatibleContourJoinBankData compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts W geometry e i side
local notation "Join[" e "," i "," side "]" =>
  K.compatibleContourJoinedBank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W geometry e i side
local notation "Point[" e "," i "," side "," s "]" =>
  (Sigma.mk (Sigma.fst Data[e,i,side]) (Join[e,i,side] s) : Total Pieces)
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "Keep[" e "," i "]" => ({LastSlot[e,i],TailSlot[e,i]} : Set (BankStackSlot Stack))
local notation "LeftAt" => bankStackLeft Pieces Stack Base Gap
local notation "RightAt" => bankStackRight Pieces Stack Base Gap
local notation "Banks" => bankSeams LeftAt RightAt
local notation "SelectedLeft[" keep "]" => fun (slot : Subtype (keep :
    Set (BankStackSlot Stack))) (t : ParamAt (Sigma.fst (Subtype.val slot))) =>
      LeftAt (Subtype.val slot) t
local notation "SelectedRight[" keep "]" => fun (slot : Subtype (keep :
    Set (BankStackSlot Stack))) (t : ParamAt (Sigma.fst (Subtype.val slot))) =>
      RightAt (Subtype.val slot) t
local notation "Selected[" e "," i "]" => bankSeams
  SelectedLeft[Keep[e,i]] SelectedRight[Keep[e,i]]
local notation "Pair[" e "," i "]" => bankPairGlue Pieces Join[e,i,false] Join[e,i,true]
local notation "Zero" => (Subtype.mk (0 : ℝ) (by norm_num) : BankJoinTime)

/-- Each signed seam parameter names one pair on one original slot. Both tags are exact. -/
theorem compatibleContourJoinedBank_originalSlot
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (s : BankJoinTime) :
    ∃ slot : Keep[edge,i], ∃ t : ParamAt slot.val.1,
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
    exact K.compatibleContourJoinedBank_finite compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W geometry edge i side t
  · let t : ℝ≥0 := ⟨s.val, le_of_not_gt before⟩
    refine ⟨⟨TailSlot[edge,i], Set.mem_insert_of_mem _ (Set.mem_singleton _)⟩, t, fun side => ?_⟩
    exact K.compatibleContourJoinedBank_tail compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W geometry edge i side t

/-- The two selected original slot relations are exactly the joined signed relation. -/
theorem compatibleContourJoinedBank_seams
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (x y : Total Pieces) :
    Pair[edge,i] x y ↔ Selected[edge,i] x y := by
  constructor
  · rintro ⟨s, hx, hy⟩
    obtain ⟨slot, t, eq⟩ := K.compatibleContourJoinedBank_originalSlot compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W geometry edge i s
    exact ⟨slot, t, hx.trans (eq false), hy.trans (eq true)⟩
  · rintro ⟨⟨slot, keep⟩, t, hx, hy⟩
    rcases Set.mem_insert_iff.mp keep with hf | ht
    · subst slot
      let f := K.compatibleContourJoinedBank_finite compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W geometry edge i
      exact ⟨bankJoinFiniteTime t, hx.trans (f false t).symm, hy.trans (f true t).symm⟩
    · have eq := Set.mem_singleton_iff.mp ht
      subst slot
      let f := K.compatibleContourJoinedBank_tail compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W geometry edge i
      exact ⟨bankJoinTailTime t, hx.trans (f false t).symm, hy.trans (f true t).symm⟩

private theorem compatibleContourJoinedBank_speed_eq
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1))
    {a b : ℝ} (apos : 0 < a) (bpos : 0 < b)
    (left : ∀ s, edist (Join[edge,i,false] Zero) (Join[edge,i,false] s) =
      ENNReal.ofReal (|s.val| * a))
    (right : ∀ s, edist (Join[edge,i,true] Zero) (Join[edge,i,true] s) =
      ENNReal.ofReal (|s.val| * b)) : a = b := by
  let slot := TailSlot[edge,i]
  have rep (side : Bool) (t : ℝ≥0) :=
    K.compatibleContourJoinedBank_tail compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W geometry edge i side t
  have bm := K.compatibleContourBaseMark_metric compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W Models
  have gm := K.compatibleContourGapMark_metric compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W Models
  have distance : faceCost Pieces (LeftAt slot 0) (LeftAt slot 1) =
      faceCost Pieces (RightAt slot 0) (RightAt slot 1) := by
    rw [bankStackLeft_curve, bankStackLeft_curve, bankStackRight_curve, bankStackRight_curve,
      faceCost_same_tag, faceCost_same_tag]
    exact bankStackCurves_same_metric Stack Pieces Base Gap bm gm slot 0 1
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
theorem compatibleContourTerminalJoin_pair_planarBall
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) :
    HasMetricBallChart ℂ (point Pieces Pair[edge,i] Point[edge,i,false,Zero]) := by
  obtain ⟨lc, a, apos, lm, r₁, ⟨L⟩⟩ := K.compatibleContourJoinedBank_charts compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W geometry edge i false
  obtain ⟨rc, b, bpos, rm, r₂, ⟨B⟩⟩ := K.compatibleContourJoinedBank_charts compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W geometry edge i true
  have speed := K.compatibleContourJoinedBank_speed_eq compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W geometry edge i apos bpos lm rm
  subst b
  have available : (Zero).val ∈ interior (Set.range (Subtype.val : BankJoinTime → ℝ)) := by
    rw [Subtype.range_coe]
    change (0 : ℝ) ∈ interior (Set.Ici (-1 : ℝ))
    rw [interior_Ici]
    exact neg_one_lt_zero
  have away (side : Bool) (s : BankJoinTime) :
      Point[edge,i,side,Zero] ≠ Point[edge,i,!side,s] := by
    intro equal
    obtain ⟨slot, t, labels⟩ := K.compatibleContourJoinedBank_originalSlot compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W geometry edge i s
    have at_zero := K.compatibleContourJoinedBank_tail compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W geometry edge i side 0
    have h : Endpoint (!side) slot.val t = Endpoint side TailSlot[edge,i] 0 :=
      (labels (!side)).symm.trans (equal.symm.trans at_zero)
    have named := K.compatibleContourTerminalJoin_endpoint_eq compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W Models geometry edge i side
      (!side) slot.val t h
    exact (Bool.not_eq_self side).mp named.1
  refine bankPair_planarBall_of_charts Pieces Join[edge,i,false] Join[edge,i,true]
    Zero Subtype.val (R₁ := r₁) (R₂ := r₂) ?_ ?_ apos available ?_ ?_ lc rc
      (away true) (away false)
  · simpa only [sub_zero] using L
  · simpa only [sub_zero] using B
  · simpa only [sub_zero] using lm
  · simpa only [sub_zero] using rm

/-- The actual full graft has a whole planar ball at every original terminal join. -/
theorem compatibleContourTerminalJoin_planarBall
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) :
    HasMetricBallChart ℂ (point Pieces Banks (LeftAt TailSlot[edge,i] 0)) := by
  let seam := K.compatibleContourJoinedBank_seams compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W geometry edge i
  let E := changeSeamsIsometryEquiv Pieces (R := Pair[edge,i]) (S := Selected[edge,i])
    (fun a b h => point_eq_of_glue Pieces ((seam a b).mp h))
    (fun a b h => point_eq_of_glue Pieces ((seam a b).mpr h))
  let x := Point[edge,i,false,Zero]
  let y := LeftAt TailSlot[edge,i] 0
  have center : E (point Pieces Pair[edge,i] x) = point Pieces Selected[edge,i] y :=
    congrArg (point Pieces Selected[edge,i])
      (K.compatibleContourJoinedBank_tail compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W geometry edge i false 0)
  have joined := K.compatibleContourTerminalJoin_pair_planarBall compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W geometry edge i
  have plane : HasMetricBallChart ℂ (point Pieces Selected[edge,i] y) := by
    rw [← center]
    exact joined.isometryEquiv E
  obtain ⟨r, rpos, A, exact_center⟩ := K.compatibleContourTerminalJoin_selectedSlots_ball
    compact nonempty R no_boundary level higher M positive inner_disk beta acute contour
    starts W Models geometry edge i
  exact plane.of_centered_ball_equiv rpos A exact_center

end Unfoldings.ConvexRoof
