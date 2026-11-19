module

public import Unfoldings.Roof.CompatibleContourPhysicalAgreement

/-! Complete actual gap and roof tails retain their exact common spatial labels. -/

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

local instance contourPhysicalTailMeshFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
local notation "LengthAt[" q "," e "]" => TriangleComplex.positiveContourBankLength D Selection q e

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
  (models : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    BankGapModel
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance contourPhysicalTailWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Index" => K.compatibleContourCellIndex compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models

local notation "PhysicalAt[" e "]" => K.compatibleContourPhysicalBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "FoldAt[" e "]" => K.compatibleContourGapFrontierMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts models e
local notation "PositionAt[" vertex "]" => SpatialFolding.toSpace
  (SpatialEnvelope.Triangulation.pairedFolding
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) Set.univ
  (TriangleComplex.vertexPoint D Set.univ vertex)
local notation "IndexAt[" vertex "," nonroot "," event "," member "]" =>
  TriangleComplex.contourGapBankIndex D Selection contour vertex nonroot event
    (Iff.mpr (TriangleComplex.mem_contourEdgeGapStack D Selection contour vertex event)
      (Iff.mp (TriangleComplex.mem_contourSavedGapStack D Selection contour vertex event) member))
local notation "ParentAt[" vertex "," nonroot "," side "," time "]" =>
  K.compatibleContourParentMark compact nonempty R no_boundary level higher M positive inner_disk
    beta acute contour starts W vertex nonroot side time

local notation "RootAt[" e "]" => K.compatibleMeshTerminalRoot compact nonempty R no_boundary
  level higher M positive inner_disk beta acute (Subtype.val e)
  (TriangleComplex.contourTerminalEdge_positive D Selection e)
local notation "SpeedAt[" e "]" => K.compatibleContourTerminalSpeed compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W e
local notation "BankSideAt[" e "," side "]" => TriangleComplex.contourParentBank D Selection contour
  (PotentialCutForest.boundary_roots Fcut) starts (Subtype.val e)
  (And.left (Subtype.property e)) side
local notation "TailAt[" e "," side "," time "]" =>
  K.compatibleContourTerminalMark compact nonempty R no_boundary level higher M positive inner_disk
    beta acute contour starts W e side time
local notation "EndAt[" e "," side "]" => K.compatibleContourParentMark compact nonempty R
  no_boundary
  level higher M positive inner_disk beta acute contour starts W (Subtype.val e)
  (And.left (Subtype.property e)) side 1

/-- Each whole original roof tail is the affine continuation of its actual final bank. -/
theorem restore_compatibleContourTerminalMark_affine
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection) (side : Bool) (t : ℝ≥0) :
    (W.partition.restoreCut R.carrier TailAt[edge,side,t]).val =
      (W.partition.restoreCut R.carrier EndAt[edge,side]).val +
        t.val • (T).pairedFolding.germDirection (BankSideAt[edge,side]).val := by
  let root := RootAt[edge]
  let speed := SpeedAt[edge]
  let time := R.terminalTime level root
  let direction := R.exterior.spatialDirection (R.terminalIndex root)
  have nonnegative : 0 ≤ time := (R.terminalTime_pos level higher _).le
  have endpoint : (W.partition.restoreCut R.carrier EndAt[edge,side]).val =
      SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex root) time) := by
    have zero := K.restore_compatibleContourTerminalMark compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W edge side 0
    have at_zero : (W.partition.restoreCut R.carrier TailAt[edge,side,0]).val =
        SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex root) time) := by
      have final_time : time + speed.val * (0 : ℝ≥0).val = time := by norm_num
      exact zero.trans (congrArg (fun r =>
        SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex root) r)) final_time)
    exact (congrArg (fun p : W.Cut => (W.partition.restoreCut R.carrier p).val)
      (K.compatibleContourTerminalMark_zero compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W edge side)).symm.trans at_zero
  have difference := R.exterior.spatial_ray_sub M (R.terminalIndex root)
    (s := time + speed.val * t.val) (t := time)
    (add_nonneg nonnegative (mul_nonneg speed.coe_nonneg t.coe_nonneg)) nonnegative
  have product : (time + speed.val * t.val - time) • direction =
      t.val • (speed.val • direction) := by
    rw [add_sub_cancel_left, smul_smul, mul_comm]
  have vector := K.compatibleContourTerminalSpeed_direction compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W edge side
  have affine : SpatialEnvelope.point M.plane
      (R.exterior.ray (R.terminalIndex root) (time + speed.val * t.val)) =
      SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex root) time) +
        t.val • (T).pairedFolding.germDirection (BankSideAt[edge,side]).val :=
    (sub_eq_iff_eq_add.mp (difference.trans (product.trans
      (congrArg (fun d : Space => t.val • d) vector.symm)))).trans (add_comm _ _)
  exact (K.restore_compatibleContourTerminalMark compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W edge side t).trans
    (affine.trans (congrArg (fun p =>
      p + t.val • (T).pairedFolding.germDirection (BankSideAt[edge,side]).val) endpoint.symm))

/-- The physical source path's true tail is the continuation of the same original terminal edge. -/
theorem compatibleContourPhysicalBank_tail_parent
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection)
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (member : event ∈ (T).pairedComplex.contourSavedGapStack (Fcut).selection contour edge.val)
    (t : ℝ≥0) :
    (PhysicalAt[event]).tail t = (W.partition.restoreCut R.carrier EndAt[edge,false]).val +
      t.val • (T).pairedFolding.germDirection (BankSideAt[edge,false]).val := by
  have last_index : IndexAt[edge.val,edge.property.1,event,member] =
      Fin.last LengthAt[contour,event] :=
    (T).pairedComplex.contourGapBankIndex_last (Fcut).selection contour edge event _
  have endpoint (s : unitInterval) :
      (PhysicalAt[event]).chain.point (Fin.last LengthAt[contour,event]) s =
        (W.partition.restoreCut R.carrier ParentAt[edge.val,edge.property.1,false,s]).val :=
    (congrArg (fun k => (PhysicalAt[event]).chain.point k s) last_index).symm.trans
      ((K.compatibleContourPhysicalBank_parent_point compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts edge.val edge.property.1 event member s).trans
        (K.restore_compatibleContourParentMark_position compact nonempty R no_boundary level higher
          M positive inner_disk beta acute contour starts W edge.val edge.property.1 false s).symm)
  have first : (W.partition.restoreCut R.carrier
      ParentAt[edge.val,edge.property.1,false,0]).val = PositionAt[edge.val] := by
    simpa only [Set.Icc.coe_zero, AffineMap.lineMap_apply_zero] using
      K.restore_compatibleContourParentMark_position compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W edge.val edge.property.1 false 0
  have last : (W.partition.restoreCut R.carrier EndAt[edge,false]).val =
      PositionAt[(Fcut).parents.parent edge.val] := by
    simpa only [Set.Icc.coe_one, AffineMap.lineMap_apply_one] using
      K.restore_compatibleContourParentMark_position compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W edge.val edge.property.1 false 1
  have vector : (W.partition.restoreCut R.carrier EndAt[edge,false]).val -
      (W.partition.restoreCut R.carrier ParentAt[edge.val,edge.property.1,false,0]).val =
        (T).pairedFolding.germDirection (BankSideAt[edge,false]).val :=
    (congrArg₂ (fun p q : Space => p - q) last first).trans
      ((T).pairedFolding.contourParentBank_direction (Fcut).selection contour (Fcut).boundary_roots
        starts edge.val edge.property.1 false).symm
  have literal {m : ℕ} (P : PolygonalChain Space (m + 1)) (s : ℝ≥0) :
      P.terminalEdgeRay.tail s = P.point (Fin.last m) 1 +
        s.val • (P.point (Fin.last m) 1 - P.point (Fin.last m) 0) := by
    simp only [PolygonalChain.point_one, PolygonalChain.point_zero, Fin.succ_last]
    rfl
  have substituted := congrArg₂ (fun p q : Space => p + t.val • (p - q)) (endpoint 1) (endpoint 0)
  exact (literal (PhysicalAt[event]).chain t).trans
    (substituted.trans (congrArg (fun v =>
      (W.partition.restoreCut R.carrier EndAt[edge,false]).val + t.val • v) vector))

/-- Both actual gap tails and the original whole roof tail carry the same physical point. -/
theorem compatibleContourGapFrontierMap_tail
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection)
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (geometry : OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (member : event ∈ (T).pairedComplex.contourSavedGapStack (Fcut).selection contour edge.val)
    (side : Bool) (t : ℝ≥0) :
    (FoldAt[event] ((models event).addressFrontier side (.inr t))).val =
      (W.partition.restoreCut R.carrier TailAt[edge,false,t]).val :=
  (congrArg Subtype.val
    (K.compatibleContourGapFrontierMap_address compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts models event geometry side (.inr t))).trans
    ((K.compatibleContourPhysicalBank_tail_parent compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W edge event member t).trans
      (K.restore_compatibleContourTerminalMark_affine compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W edge false t).symm)

end Unfoldings.ConvexRoof
