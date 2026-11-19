module

public import Unfoldings.Roof.CompatibleContourBankEmbeddings
public import Unfoldings.Geometry.BankGapBoundaryMap
public import Unfoldings.Geometry.OrientedBankGap

/-! Actual gap frontiers retain finite fibers over their original spatial bank paths. -/

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

local instance contourPhysicalBankMeshFintype : Fintype (T).Index :=
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
  (models : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    BankGapModel
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance contourPhysicalBankWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Index" => K.compatibleContourCellIndex compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models

/-- The original physical source path and its true final-edge continuation, before rolling. -/
def compatibleContourPhysicalBank
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour) :
    PolygonalRay Space (LengthAt[contour,event] + 1) :=
  ((T).pairedFolding.boundarySpatialChain
    ChainAt[contour,starts,event.val,event.property.1,LengthAt[contour,event],
      SpanAt[contour,event]]).terminalEdgeRay

local notation "PhysicalAt[" e "]" => K.compatibleContourPhysicalBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e

/-- Every target edge is its actual nonzero original spatial bank vector. -/
theorem compatibleContourPhysicalBank_edge_ne_zero
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (k : Fin (LengthAt[contour,event] + 1)) : (PhysicalAt[event]).chain.edge k ≠ 0 := by
  have value := (T).pairedFolding.boundarySpatialChain_edge
    ChainAt[contour,starts,event.val,event.property.1,LengthAt[contour,event],
      SpanAt[contour,event]] k
  intro zero
  exact (T).pairedFolding.germDirection_ne_zero _ (value.symm.trans zero)

/-- The true physical tail uses the actual nonzero final spatial bank vector. -/
theorem compatibleContourPhysicalBank_direction_ne_zero
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour) :
    (PhysicalAt[event]).direction ≠ 0 :=
  K.compatibleContourPhysicalBank_edge_ne_zero compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts event (Fin.last LengthAt[contour,event])

/-- The whole actual gap frontier maps back to the original spatial path with its
original finite-edge and true-tail parameters. -/
def compatibleContourGapFrontierMap
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour) :
    frontier (models event).region → (PhysicalAt[event]).carrier :=
  (models event).frontierMap (PhysicalAt[event])

local notation "FoldAt[" e "]" => K.compatibleContourGapFrontierMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts models e

/-- Both actual gap banks keep all physical parameters. The radial geometry used here
is the one constructed uniformly by the canonical contour-graft theorem. -/
theorem compatibleContourGapFrontierMap_address
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (geometry : OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (side : Bool) (addr : PolygonalRay.Address (LengthAt[contour,event] + 1)) :
    FoldAt[event] ((models event).addressFrontier side addr) =
      ⟨(PhysicalAt[event]).addressPoint addr, (PhysicalAt[event]).addressPoint_mem addr⟩ :=
  (models event).frontierMap_address geometry.first_outward
    (K.compatibleContourGapBank_edge_ne_zero compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts models event false)
    geometry.first_nonzero geometry.second_outward
    (K.compatibleContourGapBank_edge_ne_zero compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts models event true)
    geometry.second_nonzero geometry.common (PhysicalAt[event]) side addr

/-- The actual whole gap frontier has finite fibers over every original physical point;
this is derived from actual bank geometry, without assuming the final unfolding. -/
theorem finite_compatibleContourGapFrontierMap_fiber
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (geometry : OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (p : Space) : {z : frontier (models event).region | (FoldAt[event] z).val = p}.Finite := by
  classical
  by_cases member : p ∈ (PhysicalAt[event]).carrier
  · have finite := (models event).finite_frontierMap_fiber geometry.first_outward
      (K.compatibleContourGapBank_edge_ne_zero compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts models event false)
      geometry.first_nonzero geometry.second_outward
      (K.compatibleContourGapBank_edge_ne_zero compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts models event true)
      geometry.second_nonzero geometry.common (PhysicalAt[event])
      (K.compatibleContourPhysicalBank_edge_ne_zero compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts event)
      (K.compatibleContourPhysicalBank_direction_ne_zero compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts event) ⟨p, member⟩
    exact finite.subset (fun _ named => Subtype.ext named)
  · apply Set.finite_empty.subset
    intro z named
    exact (member (named ▸ (FoldAt[event] z).property)).elim

end Unfoldings.ConvexRoof
