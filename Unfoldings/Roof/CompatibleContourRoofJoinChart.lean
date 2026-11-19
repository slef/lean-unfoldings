module

public import Unfoldings.Roof.CompatibleContourTerminalSideLabels
public import Unfoldings.Roof.CompatibleTerminalNormalizedChart
public import Unfoldings.Geometry.StraightGapJoinBank

/-! A terminal roof chart preserves the connected finite bank and the actual unbounded tail. -/

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

local instance contourRoofJoinChartMeshFintype : Fintype (T).Index :=
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

local instance contourRoofJoinChartWholeFintype : Fintype W.Index := W.finiteIndex

local notation "ParentAt[" vertex "," nonroot "," side "," time "]" =>
  K.compatibleContourParentMark compact nonempty R no_boundary level higher M positive inner_disk
    beta acute contour starts W vertex nonroot side time

local notation "RootAt[" e "]" => K.compatibleMeshTerminalRoot compact nonempty R no_boundary
  level higher M positive inner_disk beta acute (Subtype.val e)
  (TriangleComplex.contourTerminalEdge_positive D Selection e)
local notation "SpeedAt[" e "]" => K.compatibleContourTerminalSpeed compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W e
local notation "Edge" => TriangleComplex.ContourTerminalEdge D Selection


local notation "TailAt[" e "," side "," t "]" => K.compatibleContourTerminalMark compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts W e side t
local notation "TimeAt[" e "]" => NNReal.mk (R.terminalTime level RootAt[e])
  (LT.lt.le (CompatiblePotentialRouting.terminalTime_pos R level higher RootAt[e]))


local notation "EndAt[" e "," side "]" =>
  ParentAt[Subtype.val e,And.left (Subtype.property e),side,1]
local notation "RoofBank[" e "," side "]" => joinedBank
  (ParentAt[Subtype.val e,And.left (Subtype.property e),side,·]) (TailAt[e,side,·])

/-- A finite bank segment at positive time follows the original whole bank selected at its
actual terminal endpoint. This identifies the original copies across the named join. -/
theorem compatibleContourTerminalParentMark_wholeBank (edge : Edge) (side label : Bool)
    (endpoint : EndAt[edge,side] =
      K.wholeTerminalBank compact nonempty R no_boundary W RootAt[edge] label TimeAt[edge])
    (s : unitInterval)
    (positive_time : 0 < (TimeAt[edge]).val - (1 - s.val) * (SpeedAt[edge]).val) :
    ParentAt[edge.val,edge.property.1,side,s] =
      K.wholeTerminalBank compact nonempty R no_boundary W RootAt[edge] label
        ⟨_, positive_time.le⟩ := by
  let root := RootAt[edge]
  let τ := TimeAt[edge]
  let d := SpeedAt[edge]
  let A := Set.Icc s.val (1 : ℝ)
  let : ConnectedSpace A := Subtype.connectedSpace
    ⟨Set.nonempty_Icc.mpr s.property.2, isPreconnected_Icc⟩
  let unit (x : A) : unitInterval := ⟨x.val, s.property.1.trans x.property.1, x.property.2⟩
  have time_pos (x : A) : 0 < τ.val - (1 - x.val) * d.val :=
    positive_time.trans_le (sub_le_sub_left
      (mul_le_mul_of_nonneg_right (sub_le_sub_left x.property.1 1) d.property) _)
  let time (x : A) : ℝ≥0 := ⟨_, (time_pos x).le⟩
  let mark (x : A) := ParentAt[edge.val,edge.property.1,side,unit x]
  have continuous : Continuous mark :=
    (Dilation.lipschitzWith (K.compatibleContourParentDilation compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W edge.val
      edge.property.1 side)).continuous.comp (continuous_subtype_val.subtype_mk _)
  obtain ⟨named, agrees⟩ := K.wholeTerminalBank_side_constant compact nonempty R no_boundary
    W root mark continuous time time_pos
      (fun x => K.compatibleContourTerminalParentMark_horizontal compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts W edge side (unit x))
  let one : A := ⟨1, s.property.2, le_rfl⟩
  have at_one : time one = τ := by
    apply Subtype.ext
    change τ.val - (1 - 1) * d.val = τ.val
    rw [sub_self, zero_mul, sub_zero]
  have mark_one : mark one = K.wholeTerminalBank compact nonempty R no_boundary W root label
      (time one) := endpoint.trans (congrArg
        (K.wholeTerminalBank compact nonempty R no_boundary W root label) at_one.symm)
  have same : named = label := by
    by_contra h
    exact K.wholeTerminalBank_ne compact nonempty R no_boundary W root named label h
      (time one) (time one) (time_pos one) ((agrees one).symm.trans mark_one)
  let first : A := ⟨s.val, le_rfl, s.property.2⟩
  exact same ▸ agrees first

local notation "BankAt[" e "," side "]" => TriangleComplex.contourParentBank D Selection contour
  (PotentialCutForest.boundary_roots Fcut) starts (Subtype.val e)
    (And.left (Subtype.property e)) side
local notation "Speed[" e "]" => TriangleComplex.boundaryBankLength D BankAt[e,false]

/-- The signed parameter measures the original roof-bank arclength from the actual join,
on either the final finite edge or the true tail. -/
theorem edist_compatibleContourRoofJoinBank (edge : Edge) (side : Bool) (s : BankJoinTime) :
    edist (RoofBank[edge,side] ⟨0, by norm_num⟩) (RoofBank[edge,side] s) =
      ENNReal.ofReal (|s.val| * Speed[edge]) := by
  rw [joinedBank_zero, joinedBank]
  split
  · rename_i hs
    have low : -1 ≤ s.val := s.property
    let u : unitInterval := ⟨1 + s.val, by linarith, by linarith⟩
    rw [K.compatibleContourTerminalMark_zero]
    change edist EndAt[edge,side] ParentAt[edge.val,edge.property.1,side,u] = _
    have sides : edist EndAt[edge,side] ParentAt[edge.val,edge.property.1,side,u] =
        edist EndAt[edge,false] ParentAt[edge.val,edge.property.1,false,u] := by
      cases side
      · rfl
      · exact (K.edist_compatibleContourParentMark_sides compact nonempty R no_boundary level
          higher M positive inner_disk beta acute contour starts W edge.val edge.property.1
          1 u).symm
    let bank := BankAt[edge,false]
    have length := (K.compatibleWholeMap_edist_bank compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W bank 1 u).trans
        ((T).pairedFolding.edist_directedBoundaryPath_eq_length bank 1 u)
    refine sides.trans (length.trans ?_)
    have time : edist (1 : unitInterval) u = ENNReal.ofReal |s.val| := by
      rw [edist_dist]
      change ENNReal.ofReal (dist (1 : ℝ) (1 + s.val)) = _
      rw [Real.dist_eq, sub_add_eq_sub_sub, sub_self, zero_sub, abs_neg]
    rw [time, ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
  · rename_i hs
    let u : ℝ≥0 := ⟨s.val, le_of_not_gt hs⟩
    change edist TailAt[edge,side,0] TailAt[edge,side,u] = _
    refine (K.edist_compatibleContourTerminalMark_eq_length compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W edge side 0 u).trans ?_
    have time : edist (0 : ℝ≥0) u = ENNReal.ofReal |s.val| := by
      rw [edist_dist]
      change ENNReal.ofReal (dist (0 : ℝ) s.val) = _
      rw [Real.dist_eq, zero_sub, abs_neg]
    rw [time, ENNReal.ofReal_mul (abs_nonneg _), mul_comm]

/-- A single half-plane chart follows the actual roof bank through the terminal join
with the same signed arclength on both parts. -/
theorem compatibleContourRoofJoinBank_normalized_chart (edge : Edge) (side occupied : Bool) :
    ∃ r, Nonempty (BankHalfPlaneChart (RoofBank[edge,side]) (⟨0, by norm_num⟩ : BankJoinTime)
      occupied (fun s => s.val * Speed[edge]) r) := by
  let root := RootAt[edge]
  let τ := TimeAt[edge]
  let d := SpeedAt[edge]
  let c := ‖R.exterior.spatialDirection (R.terminalIndex root)‖
  have τpos : 0 < τ.val := R.terminalTime_pos level higher root
  have cpos : 0 < c := norm_pos_iff.mpr (R.exterior.spatialDirection_ne_zero _)
  have dpos : 0 < d.val := K.compatibleContourTerminalSpeed_positive compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W edge
  have speed : Speed[edge] = d.val * c := by
    have m := K.compatibleContourTerminalSpeed_length compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W edge
    have converted : ENNReal.ofReal (d.val * c) =
        (‖R.exterior.spatialDirection (R.terminalIndex root)‖₊ : ℝ≥0∞) * d := by
      rw [ENNReal.ofReal_mul d.property,
        (show ENNReal.ofReal d.val = (d : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal), mul_comm]
      simp only [c, ofReal_norm, enorm_eq_nnnorm]
    exact (ENNReal.ofReal_eq_ofReal_iff ((D).boundaryBankLength_pos _).le
      (mul_nonneg dpos.le cpos.le)).mp (m.symm.trans converted.symm)
  obtain ⟨label, agrees⟩ := K.compatibleContourTerminalMark_wholeBank compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W edge side
  let tail := K.wholeTerminalBank compact nonempty R no_boundary W root label
  have tail_zero : TailAt[edge,side,0] = tail τ :=
    (agrees 0).trans (congrArg tail (forwardBankParameter_zero _ _))
  have endpoint : EndAt[edge,side] = tail τ :=
    (K.compatibleContourTerminalMark_zero compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W edge side).symm.trans tail_zero
  let bank := RoofBank[edge,side]
  let zero : BankJoinTime := ⟨0, by norm_num⟩
  have center : bank zero = tail τ := (joinedBank_zero _ _).trans tail_zero
  obtain ⟨ε, ⟨C⟩⟩ := K.exists_wholeTerminalBank_normalized_chart compact nonempty R no_boundary
    W root label occupied τ τpos
  let radius := min ε (τ.val * c)
  have positive_radius : 0 < radius := lt_min C.positive (mul_pos τpos cpos)
  let B := C.restrict positive_radius (min_le_left _ _)
  let move := basedEBallIsometry (IsometryEquiv.refl _) (bank zero) (tail τ) center
    (ENNReal.ofReal radius)
  refine ⟨radius, ⟨⟨positive_radius, move.trans B.chart, ?_, ?_⟩⟩⟩
  · have moved : move ⟨bank zero, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr
        positive_radius)⟩ = ⟨tail τ, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr
          positive_radius)⟩ := Subtype.ext center
    change (B.chart (move _)).val = _
    rw [moved, B.centered]
  · intro s near
    have dist := K.edist_compatibleContourRoofJoinBank compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W edge side s
    have small := dist.symm.trans_lt ((edist_comm _ _).trans_lt near)
    have time_bound : |s.val| * (d.val * c) < τ.val * c := by
      rw [speed] at small
      exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg
        (mul_nonneg (abs_nonneg _) (mul_nonneg dpos.le cpos.le))).mp small).trans_le
          (min_le_right _ _)
    have rel : |s.val| * d.val < τ.val := by
      rw [← mul_assoc] at time_bound
      exact lt_of_mul_lt_mul_right time_bound cpos.le
    have after : 0 < τ.val + d.val * s.val := by
      have h := mul_le_mul_of_nonneg_left (neg_abs_le s.val) d.property
      nlinarith
    let p : ℝ≥0 := ⟨_, after.le⟩
    have follows : bank s = tail p := by
      unfold bank joinedBank
      split
      · rename_i hs
        have low : -1 ≤ s.val := s.property
        let u : unitInterval := ⟨1 + s.val, by linarith, by linarith⟩
        change ParentAt[edge.val,edge.property.1,side,u] = tail p
        have eq : τ.val - (1 - u.val) * d.val = p.val := by
          change τ.val - (1 - (1 + s.val)) * d.val = τ.val + d.val * s.val
          ring
        have h : 0 < τ.val - (1 - u.val) * d.val := eq.symm ▸ after
        have mark := K.compatibleContourTerminalParentMark_wholeBank compact nonempty R
          no_boundary level higher M positive inner_disk beta acute contour starts W edge
          side label endpoint u h
        exact mark.trans (congrArg tail (Subtype.ext eq))
      · exact agrees ⟨s.val, le_of_not_gt (by assumption)⟩
    have close : tail p ∈ Metric.eball (tail τ) (ENNReal.ofReal radius) := by
      change edist (tail p) (tail τ) < _
      change edist (bank s) (bank zero) < _ at near
      rwa [follows, center] at near
    have moved : move ⟨bank s, near⟩ = ⟨tail p, close⟩ := Subtype.ext follows
    change (B.chart (move _)).val.val = _
    rw [moved, B.parameter p close]
    exact congrArg Complex.ofReal (by
      change (τ.val + d.val * s.val - τ.val) * c = s.val * Speed[edge]
      rw [speed]
      ring)

end Unfoldings.ConvexRoof
