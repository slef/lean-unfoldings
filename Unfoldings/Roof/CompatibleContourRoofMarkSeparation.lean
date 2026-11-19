module

public import Unfoldings.Roof.CompatibleContourParentMarkUniqueness
public import Unfoldings.Roof.CompatibleContourTerminalMarks
public import Unfoldings.Roof.TerminalBands

/-! The actual completion height separates finite bank interiors from whole terminal tails. -/

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

local instance contourRoofMarkMeshFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "ChainAt[" q "," h "," i "," hf "," n "," hn "]" =>
  K.compatibleMeshFreshSourceBankChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h i hf n hn

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
local notation "LengthAt[" q "," e "]" => TriangleComplex.positiveContourBankLength D Selection q e
local notation "SpanAt[" q "," e "]" => TriangleComplex.positiveContourBank_span D Selection q e

local notation "BankAt[" q "," h "," e "]" =>
  K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e
local notation "OpenedAt[" q "," h "," e "]" =>
  K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive inner_disk
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

local instance contourRoofMarkWholeFintype : Fintype W.Index := W.finiteIndex

local notation "PathAt[" v "," h "," side "," t "]" => TriangleComplex.directedBoundaryPath D
  (TriangleComplex.contourParentBank D Selection contour (PotentialCutForest.boundary_roots Fcut)
    starts v h side) t
local notation "ParentAt[" v "," h "," side "," t "]" => K.compatibleContourParentMark compact
  nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W v h side t
local notation "TailAt[" e "," side "," t "]" => K.compatibleContourTerminalMark compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts W e side t
local notation "RootAt[" e "]" => K.compatibleMeshTerminalRoot compact nonempty R no_boundary
  level higher M positive inner_disk beta acute (Subtype.val e)
  (TriangleComplex.contourTerminalEdge_positive D Selection e)
local notation "SpeedAt[" e "]" => K.compatibleContourTerminalSpeed compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W e

/-- Every actual closed finite bank stays in the original completion sublevel. -/
theorem compatibleContourParentMark_height_le
    (vertex : (D).Vertex Set.univ) (nonroot : vertex ∉ (Fcut).parents.roots)
    (side : Bool) (t : unitInterval) :
    (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut R.carrier ParentAt[vertex,nonroot,side,t]).val)
        ≤ level := by
  have position := K.restore_compatibleMeshWholeMap compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W PathAt[vertex,nonroot,side,t]
  have member := (T).toTriangulation.fold_horizontal_mem_clip (Fcut).retain
    PathAt[vertex,nonroot,side,t]
  rw [M.clip_eq_sublevel, neg_neg] at member
  exact (congrArg (fun p : Space => (K.clippedExtension slopes compact nonempty).height
    (Cap.horizontal p)) position).trans_le member

/-- Every strict finite time stays below the rim in its literal whole-cut metric copy. -/
theorem compatibleContourParentMark_height_lt
    (vertex : (D).Vertex Set.univ) (nonroot : vertex ∉ (Fcut).parents.roots)
    (side : Bool) (t : unitInterval) (before : t < 1) :
    (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut R.carrier ParentAt[vertex,nonroot,side,t]).val)
        < level :=
  (congrArg (fun p : Space => (K.clippedExtension slopes compact nonempty).height
    (Cap.horizontal p)) (K.restore_compatibleMeshWholeMap compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W PathAt[vertex,nonroot,side,t])).trans_lt
    (K.compatibleContourParentPath_height_lt compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts vertex nonroot side t before)

/-- Actual whole terminal tails stay on or above their original completion level. -/
theorem compatibleContourTerminalMark_height_ge
    (edge : (D).ContourTerminalEdge Selection) (side : Bool) (t : ℝ≥0) :
    level ≤ (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut R.carrier TailAt[edge,side,t]).val) := by
  have position := congrArg (fun p : Space => Cap.horizontal p)
    (K.restore_compatibleContourTerminalMark compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W edge side t)
  simp only [SpatialEnvelope.horizontal_point] at position
  have nonnegative := add_nonneg (R.terminalTime_pos level higher RootAt[edge]).le
    (mul_nonneg (SpeedAt[edge]).property t.property)
  have bound := (R.terminal_ray_superlevel_iff level higher RootAt[edge] nonnegative).mpr
    (le_add_of_nonneg_right (mul_nonneg (SpeedAt[edge]).property t.property))
  exact bound.trans_eq (congrArg (K.clippedExtension slopes compact nonempty).height
    position).symm

/-- Every positive actual tail parameter lies strictly above the finite roof sublevel. -/
theorem compatibleContourTerminalMark_height_gt
    (edge : (D).ContourTerminalEdge Selection) (side : Bool) (t : ℝ≥0) (positive_time : 0 < t) :
    level < (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut R.carrier TailAt[edge,side,t]).val) := by
  have position := congrArg (fun p : Space => Cap.horizontal p)
    (K.restore_compatibleContourTerminalMark compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W edge side t)
  simp only [SpatialEnvelope.horizontal_point] at position
  have duration := mul_pos (K.compatibleContourTerminalSpeed_positive compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W edge)
    (show (0 : ℝ) < t.val from positive_time)
  have nonnegative := add_nonneg (R.terminalTime_pos level higher RootAt[edge]).le duration.le
  have bound : level < (K.clippedExtension slopes compact nonempty).height
      (R.exterior.ray (R.terminalIndex RootAt[edge])
        (R.terminalTime level RootAt[edge] + (SpeedAt[edge]).val * t.val)) := by
    apply lt_of_not_ge
    intro below
    have time_bound := (R.terminal_ray_sublevel_iff level higher RootAt[edge] nonnegative).mp below
    linarith
  exact bound.trans_eq (congrArg (K.clippedExtension slopes compact nonempty).height
    position).symm

/-- No closed whole-tail mark is any strict finite roof-bank mark, on either side. -/
theorem compatibleContourTerminalMark_ne_parent_interior
    (edge : (D).ContourTerminalEdge Selection) (tail_side : Bool) (s : ℝ≥0)
    (vertex : (D).Vertex Set.univ) (nonroot : vertex ∉ (Fcut).parents.roots)
    (side : Bool) (t : unitInterval) (before : t < 1) :
    TailAt[edge,tail_side,s] ≠ ParentAt[vertex,nonroot,side,t] := by
  intro equal
  have lower := K.compatibleContourTerminalMark_height_ge compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W edge tail_side s
  have upper := K.compatibleContourParentMark_height_lt compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W vertex nonroot side t before
  exact (not_lt_of_ge lower) ((congrArg (fun x =>
    (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut R.carrier x).val)) equal).trans_lt upper)

/-- No positive whole-tail mark is any closed finite roof-bank mark. The actual zero
parameter is deliberately excluded because it is the original finite endpoint copy. -/
theorem compatibleContourParentMark_ne_terminal_positive
    (vertex : (D).Vertex Set.univ) (nonroot : vertex ∉ (Fcut).parents.roots)
    (side : Bool) (s : unitInterval) (edge : (D).ContourTerminalEdge Selection)
    (tail_side : Bool) (t : ℝ≥0) (positive_time : 0 < t) :
    ParentAt[vertex,nonroot,side,s] ≠ TailAt[edge,tail_side,t] := by
  intro equal
  have upper := K.compatibleContourParentMark_height_le compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W vertex nonroot side s
  have lower := K.compatibleContourTerminalMark_height_gt compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W edge tail_side t positive_time
  exact (not_lt_of_ge upper) (lower.trans_eq
    (congrArg (fun x => (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut R.carrier x).val)) equal).symm)

end Unfoldings.ConvexRoof
