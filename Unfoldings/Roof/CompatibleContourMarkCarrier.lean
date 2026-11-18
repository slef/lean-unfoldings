module

public import Unfoldings.Roof.CompatibleContourGraft
public import Unfoldings.Roof.WholeCutMarkBoundary

/-! All actual finite and infinite original roof attachment marks lie over its forest cuts. -/

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
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance contourMarkCarrierMeshFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "SourceAt[" q "," i "]" => TriangleComplex.contourOriginalVertex
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) q i
local notation "RetainAt[" q "," i "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut)
  (TriangleComplex.contourFrontier
    (SpatialEnvelope.Triangulation.pairedComplex
      (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
    (PotentialCutForest.selection Fcut) q i)

local notation "ChainAt[" q "," h "," i "," hf "," n "," hn "]" =>
  K.compatibleMeshFreshSourceBankChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h i hf n hn

local notation "cap" => SpatialEnvelope.Triangulation.normalizedCap
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "RollAt[" q "," h "," i "," hf "," n "," hn "]" => TriangleComplex.boundaryChainRoll
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) ChainAt[q,h,i,hf,n,hn]

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
local notation "LengthAt[" q "," e "]" => TriangleComplex.positiveContourBankLength D Selection q e
local notation "SpanAt[" q "," e "]" => TriangleComplex.positiveContourBank_span D Selection q e
local notation "VertexAt[" q "," e "]" => TriangleComplex.positiveContourVertex D Selection q e

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

local instance contourMarkCarrierWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W

local notation "RootAt[" e "]" => K.compatibleMeshTerminalRoot compact nonempty R no_boundary
  level higher M positive inner_disk beta acute (Subtype.val e)
  (TriangleComplex.contourTerminalEdge_positive D Selection e)
local notation "EndAt[" e "," side "]" =>
  K.compatibleContourParentMark compact nonempty R no_boundary level higher M positive inner_disk
    beta acute contour starts W (Subtype.val e) (And.left (Subtype.property e)) side 1

/-- The actual original parent-bank interpolation stays on its selected physical cut edge. -/
theorem compatibleContourParentMark_carrier (vertex : (T).pairedComplex.Vertex Set.univ)
    (nonroot : vertex ∉ (Fcut).parents.roots) (side : Bool) (t : unitInterval) :
    Cap.horizontal (W.partition.restoreCut R.carrier
      (K.compatibleContourParentMark compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W vertex nonroot side t)).val ∈ R.carrier := by
  let e : {v : (T).pairedComplex.Vertex Set.univ // v ∉ (Fcut).parents.roots} := ⟨vertex, nonroot⟩
  let s := (Fcut).selection.edge e
  have edge_eq : segment ℝ ((Q).projectedVertex vertex)
      ((Q).projectedVertex ((Fcut).parents.parent vertex)) =
        ((Q).projectedTriangle ((T).pairedComplex.left s).face).edge
          ((T).pairedComplex.left s).edge := by
    rcases (Fcut).selection.link e with ⟨first, last⟩ | ⟨first, last⟩
    · change vertex = (T).pairedComplex.seamVertex s false at first
      change (Fcut).parents.parent vertex = (T).pairedComplex.seamVertex s true at last
      rw [last, first]
      rfl
    · change vertex = (T).pairedComplex.seamVertex s true at first
      change (Fcut).parents.parent vertex = (T).pairedComplex.seamVertex s false at last
      rw [last, first, segment_symm]
      rfl
  have in_edge : AffineMap.lineMap ((Q).projectedVertex vertex)
      ((Q).projectedVertex ((Fcut).parents.parent vertex)) t.val ∈
        ((Q).projectedTriangle ((T).pairedComplex.left s).face).edge
          ((T).pairedComplex.left s).edge := edge_eq ▸
    (convex_segment _ _).lineMap_mem (left_mem_segment _ _ _) (right_mem_segment _ _ _) t.property
  have on_cut := ((R.truncatedCarrier_eq_carrier_inter_sublevel level higher).subset
    ((Fcut).selected_subset e in_edge)).1
  let bank := (T).pairedComplex.contourParentBank (Fcut).selection contour
    (Fcut).boundary_roots starts vertex nonroot side
  have projected : Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain
      ((T).pairedComplex.directedBoundaryPath bank t)) =
      AffineMap.lineMap ((Q).projectedVertex vertex)
        ((Q).projectedVertex ((Fcut).parents.parent vertex)) t.val :=
    (congrArg Cap.horizontal ((T).pairedFolding.contourParentBank_position (Fcut).selection
      contour (Fcut).boundary_roots starts vertex nonroot side t)).trans
      (Cap.horizontal.toAffineMap.apply_lineMap _ _ _)
  have whole := congrArg Cap.horizontal (K.restore_compatibleMeshWholeMap compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W
      ((T).pairedComplex.directedBoundaryPath bank t))
  exact (whole.trans projected).symm ▸ on_cut

/-- Every entire terminal continuation stays on its actual original unbounded forest ray. -/
theorem compatibleContourTerminalMark_carrier
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection) (side : Bool) (t : ℝ≥0) :
    Cap.horizontal (W.partition.restoreCut R.carrier
      (K.compatibleContourTerminalMark compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W edge side t)).val ∈ R.carrier := by
  let speed := K.compatibleContourTerminalSpeed compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W edge
  let u : ℝ≥0 := ⟨R.terminalTime level RootAt[edge] + speed.val * t.val,
    add_nonneg (R.terminalTime_pos level higher _).le (mul_nonneg speed.property t.property)⟩
  have on_ray : R.exterior.ray (R.terminalIndex RootAt[edge]) u.val ∈ R.carrier :=
    R.terminalRayCut_subset_carrier RootAt[edge] ⟨u, R.terminal_lineMap RootAt[edge] u.val⟩
  have position := (congrArg Cap.horizontal
    (K.restore_compatibleContourTerminalMark compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W edge side t)).trans
      (SpatialEnvelope.horizontal_point _ _)
  exact position.symm ▸ on_ray

end Unfoldings.ConvexRoof
