module

public import Unfoldings.Roof.CompatibleContourBankAgreement
public import Unfoldings.Complex.ContourGapTerminalIndex
public import Unfoldings.Roof.CompatibleSourceBankTerminal
public import Unfoldings.Roof.WholeTerminalContinuation

/-! Actual terminal contour banks derive the original unbounded ray and its positive speed. -/

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

local instance contourTerminalGeometryIndexFintype : Fintype (T).Index :=
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

local instance contourTerminalGeometryWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W

local notation "RootAt[" e "]" => K.compatibleMeshTerminalRoot compact nonempty R no_boundary
  level higher M positive inner_disk beta acute (Subtype.val e)
  (TriangleComplex.contourTerminalEdge_positive D Selection e)
local notation "EndAt[" e "," side "]" =>
  K.compatibleContourParentMark compact nonempty R no_boundary level higher M positive inner_disk
    beta acute contour starts W (Subtype.val e) (And.left (Subtype.property e)) side 1

/-- The actual last fine edge derives a common positive terminal speed on both original sides.
Its true endpoint copies have the exact original spatial terminal coordinates. -/
theorem exists_compatibleContourTerminalGeometry
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection) :
    ∃ d : ℝ, 0 < d ∧
      (∀ side : Bool, (T).pairedFolding.germDirection
        ((T).pairedComplex.contourParentBank (Fcut).selection contour (Fcut).boundary_roots
          starts edge.val edge.property.1 side).val =
            d • R.exterior.spatialDirection (R.terminalIndex RootAt[edge])) ∧
      ∀ side : Bool, (W.partition.restoreCut R.carrier EndAt[edge,side]).val =
        SpatialEnvelope.point M.plane (R.terminalPoint level RootAt[edge]) := by
  let bank := (T).pairedComplex.contourParentBank (Fcut).selection contour
    (Fcut).boundary_roots starts edge.val edge.property.1
  let chain := ((T).pairedComplex.boundarySystem (Fcut).retain).singleton (bank false)
  have span := (T).pairedComplex.contourTerminalEdge_span (Fcut).selection edge
  have root : (Fcut).parents.parent edge.val = (Fcut).parents.root edge.val := by
    have reaches := (Fcut).parents.iterate_distanceToRoot_eq_root edge.val
    simpa only [span, Function.iterate_one] using reaches
  have labels (k : Fin 1) : (T).pairedComplex.vertexForgetCuts (Set.subset_univ _)
      ((T).pairedComplex.boundaryEndVertex _ (chain.point k)) =
        (Fcut).parents.parent^[k.val] edge.val := by
    have only : k = 0 := Subsingleton.elim _ _
    subst k
    exact (T).pairedComplex.contourParentBank_start (Fcut).selection contour
      (Fcut).boundary_roots starts edge.val edge.property.1 false
  have terminal : (T).pairedComplex.vertexForgetCuts (Set.subset_univ _)
      ((T).pairedComplex.boundaryEndVertex _ ((T).pairedComplex.boundaryTurn _ chain.last)) =
        (Fcut).parents.root edge.val :=
    ((T).pairedComplex.contourParentBank_finish (Fcut).selection contour (Fcut).boundary_roots
      starts edge.val edge.property.1 false).trans root
  obtain ⟨d, positive_d, last, direction, _, _⟩ :=
    K.exists_compatibleSourceBank_terminal_geometry compact nonempty R no_boundary level higher
      M positive inner_disk beta acute chain edge.val span labels terminal
  have vector : (T).pairedFolding.germDirection (bank false).val =
      d • R.exterior.spatialDirection (R.terminalIndex RootAt[edge]) :=
    ((T).pairedFolding.boundarySpatialChain_edge chain (Fin.last 0)).symm.trans direction
  refine ⟨d, positive_d, ?_, ?_⟩
  · intro side
    have same := ((T).pairedFolding.contourParentBank_direction (Fcut).selection contour
      (Fcut).boundary_roots starts edge.val edge.property.1 side).trans
      ((T).pairedFolding.contourParentBank_direction (Fcut).selection contour
        (Fcut).boundary_roots starts edge.val edge.property.1 false).symm
    exact same.trans vector
  · intro side
    have physical : (T).pairedFolding.toSpace (Fcut).retain
        ((T).pairedComplex.directedBoundaryPath (bank false) 1) =
          SpatialEnvelope.point M.plane (R.terminalPoint level RootAt[edge]) := by
      change (T).pairedFolding.toSpace (Fcut).retain
        ((T).pairedComplex.directedBoundaryPath (chain.point (Fin.last 0)) 1) = _
      rw [← (T).pairedFolding.boundarySpatialChain_point chain (Fin.last 0) 1,
        PolygonalChain.point_one]
      exact last
    have same : (T).pairedFolding.toSpace (Fcut).retain
        ((T).pairedComplex.directedBoundaryPath (bank side) 1) =
        (T).pairedFolding.toSpace (Fcut).retain
          ((T).pairedComplex.directedBoundaryPath (bank false) 1) := by
      exact ((T).pairedFolding.contourParentBank_position (Fcut).selection contour
        (Fcut).boundary_roots starts edge.val edge.property.1 side 1).trans
        ((T).pairedFolding.contourParentBank_position (Fcut).selection contour
          (Fcut).boundary_roots starts edge.val edge.property.1 false 1).symm
    exact (K.restore_compatibleMeshWholeMap compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W _).trans (same.trans physical)

end Unfoldings.ConvexRoof
