module

public import Unfoldings.Roof.CompatibleContourTerminalGeometry

/-! Construct actual infinite-tail attachment marks with the original finite-edge parameter. -/

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

local instance contourTerminalMarkIndexFintype : Fintype (T).Index :=
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

local instance contourTerminalMarkWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W

local notation "RootAt[" e "]" => K.compatibleMeshTerminalRoot compact nonempty R no_boundary
  level higher M positive inner_disk beta acute (Subtype.val e)
  (TriangleComplex.contourTerminalEdge_positive D Selection e)
local notation "EndAt[" e "," side "]" =>
  K.compatibleContourParentMark compact nonempty R no_boundary level higher M positive inner_disk
    beta acute contour starts W (Subtype.val e) (And.left (Subtype.property e)) side 1

/-- The common positive terminal speed is derived from the actual original last fine edge. -/
def compatibleContourTerminalSpeed
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection) : ℝ≥0 :=
  ⟨(K.exists_compatibleContourTerminalGeometry compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W edge).choose,
    (K.exists_compatibleContourTerminalGeometry compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W edge).choose_spec.1.le⟩

local notation "SpeedAt[" e "]" => K.compatibleContourTerminalSpeed compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W e

theorem compatibleContourTerminalSpeed_positive
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection) :
    0 < (SpeedAt[edge]).val :=
  (K.exists_compatibleContourTerminalGeometry compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W edge).choose_spec.1

/-- Both actual original bank vectors use the very same chosen physical continuation speed. -/
theorem compatibleContourTerminalSpeed_direction
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection) (side : Bool) :
    (T).pairedFolding.germDirection
      ((T).pairedComplex.contourParentBank (Fcut).selection contour (Fcut).boundary_roots
        starts edge.val edge.property.1 side).val =
          (SpeedAt[edge]).val • R.exterior.spatialDirection (R.terminalIndex RootAt[edge]) :=
  (K.exists_compatibleContourTerminalGeometry compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W edge).choose_spec.2.1 side

/-- The actual finite endpoint determines a unique original whole-terminal side. -/
theorem compatibleContourTerminalEndpoint_horizontal
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection) (side : Bool) :
    Cap.horizontal (W.partition.restoreCut R.carrier EndAt[edge,side]).val =
      R.exterior.ray (R.terminalIndex RootAt[edge]) (R.terminalTime level RootAt[edge]) :=
  (congrArg Cap.horizontal
    ((K.exists_compatibleContourTerminalGeometry compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W edge).choose_spec.2.2 side)).trans
      (SpatialEnvelope.horizontal_point _ _)

/-- Continue the two literal original endpoint copies at the last fine edge's genuine speed.
The original whole-terminal side is recovered from each actual endpoint, not supplied. -/
def compatibleContourTerminalMark
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection) (side : Bool) (t : ℝ≥0) :
    W.Cut :=
  K.wholeTerminalContinuation compact nonempty R no_boundary W RootAt[edge]
    ⟨R.terminalTime level RootAt[edge], (R.terminalTime_pos level higher _).le⟩
    (R.terminalTime_pos level higher _) EndAt[edge,side]
    (K.compatibleContourTerminalEndpoint_horizontal compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W edge side) SpeedAt[edge] t

local notation "TailAt[" e "," side "," t "]" =>
  K.compatibleContourTerminalMark compact nonempty R no_boundary level higher M positive
    inner_disk beta acute contour starts W e side t

/-- Every whole tail starts at exactly its original finite-bank endpoint copy. -/
@[simp] theorem compatibleContourTerminalMark_zero
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection) (side : Bool) :
    TailAt[edge,side,0] = EndAt[edge,side] :=
  K.wholeTerminalContinuation_zero compact nonempty R no_boundary W _ _ _ _ _ _

/-- All infinite-tail bank marks retain the original physical roof coordinates. -/
theorem restore_compatibleContourTerminalMark
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection) (side : Bool) (t : ℝ≥0) :
    (W.partition.restoreCut R.carrier TailAt[edge,side,t]).val =
      SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex RootAt[edge])
        (R.terminalTime level RootAt[edge] + (SpeedAt[edge]).val * t.val)) :=
  K.restore_wholeTerminalContinuation compact nonempty R no_boundary W _ _ _ _ _ _ _

/-- Exact distances on either entire roof tail use the same parameter as its last finite edge. -/
theorem edist_compatibleContourTerminalMark
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection) (side : Bool) (s t : ℝ≥0) :
    edist TailAt[edge,side,s] TailAt[edge,side,t] =
      ((‖R.exterior.spatialDirection (R.terminalIndex RootAt[edge])‖₊ : ℝ≥0∞) * SpeedAt[edge]) *
        edist s t :=
  K.edist_wholeTerminalContinuation compact nonempty R no_boundary W _ _ _ _ _ _ _ _

/-- The derived whole-ray speed is exactly the original finite bank's full spatial length. -/
theorem compatibleContourTerminalSpeed_length
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection) :
    (‖R.exterior.spatialDirection (R.terminalIndex RootAt[edge])‖₊ : ℝ≥0∞) * SpeedAt[edge] =
      ENNReal.ofReal ((T).pairedComplex.boundaryBankLength
        ((T).pairedComplex.contourParentBank (Fcut).selection contour (Fcut).boundary_roots
          starts edge.val edge.property.1 false)) := by
  let bank := (T).pairedComplex.contourParentBank (Fcut).selection contour
    (Fcut).boundary_roots starts edge.val edge.property.1 false
  let direction := R.exterior.spatialDirection (R.terminalIndex RootAt[edge])
  have vector := K.compatibleContourTerminalSpeed_direction compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W edge false
  have norm_value : ‖(SpeedAt[edge]).val • direction‖ = (SpeedAt[edge]).val * ‖direction‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (SpeedAt[edge]).property]
  have length := ((T).pairedFolding.boundaryBankLength_eq_germDirection_norm bank).trans
    ((congrArg norm vector).trans norm_value)
  have converted : ENNReal.ofReal ‖direction‖ = (‖direction‖₊ : ℝ≥0∞) := by
    rw [ofReal_norm, enorm_eq_nnnorm]
  have product : ENNReal.ofReal ((SpeedAt[edge]).val * ‖direction‖) =
      (SpeedAt[edge] : ℝ≥0∞) * (‖direction‖₊ : ℝ≥0∞) := by
    calc
      _ = ENNReal.ofReal (SpeedAt[edge]).val * ENNReal.ofReal ‖direction‖ :=
        ENNReal.ofReal_mul (SpeedAt[edge]).property
      _ = _ := congrArg₂ (fun x y : ℝ≥0∞ => x * y)
        (show ENNReal.ofReal (SpeedAt[edge]).val = (SpeedAt[edge] : ℝ≥0∞) from
          ENNReal.ofReal_coe_nnreal) converted
  exact (mul_comm _ _).trans (product.symm.trans (congrArg ENNReal.ofReal length.symm))

/-- Infinite roof-bank distances have the same length coefficient as the last original edge. -/
theorem edist_compatibleContourTerminalMark_eq_length
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection) (side : Bool) (s t : ℝ≥0) :
    edist TailAt[edge,side,s] TailAt[edge,side,t] =
      ENNReal.ofReal ((T).pairedComplex.boundaryBankLength
        ((T).pairedComplex.contourParentBank (Fcut).selection contour (Fcut).boundary_roots
          starts edge.val edge.property.1 false)) * edist s t :=
  (K.edist_compatibleContourTerminalMark compact nonempty R no_boundary level higher M positive
    inner_disk beta acute contour starts W edge side s t).trans
    (congrArg (fun d => d * edist s t)
      (K.compatibleContourTerminalSpeed_length compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W edge))

end Unfoldings.ConvexRoof
