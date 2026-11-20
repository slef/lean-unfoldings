module

public import Unfoldings.Complex.ContourGapBankSurjectivity
public import Unfoldings.Geometry.PolygonalRayOrderedTransfer
public import Unfoldings.Roof.CompatibleMeshOrderedParents
public import Unfoldings.Roof.CompatibleContourPhysicalTails
public import Unfoldings.Roof.CompatibleContourRoofMarkSeparation

/-! The physical source banks are embedded rays with their original edge parameters. -/

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

local instance contourPhysicalOrderMeshFintype : Fintype (T).Index :=
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

local instance contourPhysicalOrderWholeFintype : Fintype W.Index := W.finiteIndex

local notation "G" => K.clippedExtension slopes compact nonempty
local notation "B" => SlopeEnvelope.boundaryEnvelope G boundary
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Roof" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "VertexAt[" q "," e "]" => TriangleComplex.positiveContourVertex D Selection q e
local notation "SpanAt[" q "," e "]" => TriangleComplex.positiveContourBank_span D Selection q e
local notation "PhysicalAt[" e "]" => K.compatibleContourPhysicalBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "BaseAt[" v "," h "," t "]" => K.compatibleContourParentMark compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts W v h false t
local notation "TailAt[" e "," t "]" => K.compatibleContourTerminalMark compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts W e false t

set_option maxHeartbeats 600000 in
-- The original spatial chain and compatible projected mesh have large dependent types.
/-- Original physical finite banks ascend strictly along their entire closed edges. -/
theorem compatibleContourPhysicalBank_strictPotential
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (i : Fin (LengthAt[contour,event] + 1)) :
    StrictMono ((B).height ∘ Cap.horizontal ∘ (PhysicalAt[event]).chain.point i) := by
  let v := (Fcut).parents.parent^[i.val] VertexAt[contour,event]
  have nonroot : v ∉ (Fcut).parents.roots :=
    (Fcut).parents.iterate_lt_distanceToRoot_not_mem VertexAt[contour,event]
      (by rw [SpanAt[contour,event]]; exact i.isLt)
  have eq (t : unitInterval) : Cap.horizontal ((PhysicalAt[event]).chain.point i t) =
      AffineMap.lineMap ((Roof).projectedVertex v)
        ((Roof).projectedVertex ((Fcut).parents.parent v)) t.val := by
    rw [K.compatibleContourPhysicalBank_point compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts event i]
    simp only [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub]
    rfl
  intro t u before
  change (B).height (Cap.horizontal ((PhysicalAt[event]).chain.point i t)) <
    (B).height (Cap.horizontal ((PhysicalAt[event]).chain.point i u))
  rw [eq t, eq u]
  exact K.compatibleMeshParentEdge_strictPotential compact nonempty R no_boundary level higher
    positive inner_disk beta acute M v nonroot before

set_option maxHeartbeats 600000 in
-- The original bank addresses are transferred into the finite whole-cut model.
include W in
/-- Positive physical tail time is separated from all finite banks by the completion level. -/
theorem compatibleContourPhysicalBank_tail_ne_finite
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (i : Fin (LengthAt[contour,event] + 1)) (t : unitInterval) (s : ℝ≥0) (pos : 0 < s) :
    (PhysicalAt[event]).tail s ≠ (PhysicalAt[event]).chain.point i t := by
  obtain ⟨v, nonroot, member, index⟩ :=
    (D).exists_contourGapBankIndex_eq Selection contour event i
  have on_stack : event ∈ (D).contourSavedGapStack Selection contour v :=
    ((D).mem_contourSavedGapStack Selection contour v event).mpr
      (((D).mem_contourEdgeGapStack Selection contour v event).mp member)
  have finite_eq : (PhysicalAt[event]).chain.point i t =
      (W.partition.restoreCut R.carrier BaseAt[v,nonroot,t]).val :=
    (congrArg (fun k => (PhysicalAt[event]).chain.point k t) index).symm.trans
      ((K.compatibleContourPhysicalBank_parent_point compact nonempty R no_boundary level higher
        M positive inner_disk beta acute contour starts v nonroot event on_stack t).trans
        (K.restore_compatibleContourParentMark_position compact nonempty R no_boundary level
          higher M positive inner_disk beta acute contour starts W v nonroot false t).symm)
  obtain ⟨edge, terminal⟩ := (D).exists_contourTerminalEdge_mem_gapStack Selection contour event
  have tail_eq : (PhysicalAt[event]).tail s =
      (W.partition.restoreCut R.carrier TailAt[edge,s]).val :=
    (K.compatibleContourPhysicalBank_tail_parent compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W edge event terminal s).trans
      (K.restore_compatibleContourTerminalMark_affine compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W edge false s).symm
  have below := K.compatibleContourParentMark_height_le compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W v nonroot false t
  have above := K.compatibleContourTerminalMark_height_gt compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W edge false s pos
  intro eq
  have named := congrArg (fun p => (G).height (Cap.horizontal p))
    (tail_eq.symm.trans (eq.trans finite_eq))
  exact (not_lt_of_ge (named.trans_le below)) above

set_option maxHeartbeats 600000 in
-- The edge and tail facts are combined on one dependent original bank type.
include W in
/-- Transferring a gap's normalized bank parameter to its physical path is injective. -/
theorem compatibleContourPhysicalBank_mapCarrier_injective
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (Q : PolygonalRay ℂ (LengthAt[contour,event] + 1))
    (outward : Q.Outward) (genuine : ∀ i, Q.chain.edge i ≠ 0) (nonzero : Q.direction ≠ 0) :
    Function.Injective (Q.mapCarrier PhysicalAt[event]) :=
  Q.mapCarrier_injective_of_ordered outward genuine nonzero PhysicalAt[event]
    (fun p => (B).height (Cap.horizontal p))
    (K.compatibleContourPhysicalBank_strictPotential compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts event)
    (K.compatibleContourPhysicalBank_direction_ne_zero compact nonempty R no_boundary level higher
      M positive inner_disk beta acute contour starts event)
    (K.compatibleContourPhysicalBank_tail_ne_finite compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W event)

end Unfoldings.ConvexRoof
