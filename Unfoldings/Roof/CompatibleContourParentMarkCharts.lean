module

public import Unfoldings.Roof.CompatibleContourParentMarkUniqueness
public import Unfoldings.Boundary.HalfPlaneMetric
public import Unfoldings.Metric.RestoredPlacedBall

/-! Actual roof-bank marks retain centered whole half-plane charts and original placements. -/

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

local instance contourParentChartMeshFintype : Fintype (T).Index :=
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

local instance contourParentChartWholeFintype : Fintype W.Index := W.finiteIndex

local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Roof" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "PathAt[" v "," h "," side "," t "]" => TriangleComplex.directedBoundaryPath D
  (TriangleComplex.contourParentBank D Selection contour (PotentialCutForest.boundary_roots Fcut)
    starts v h side) t
local notation "ParentAt[" v "," h "," side "," t "]" => K.compatibleContourParentMark compact
  nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W v h side t

local notation "ParentBank[" v "," h "," side "]" => TriangleComplex.contourParentBank D Selection
  contour (PotentialCutForest.boundary_roots Fcut) starts v h side
local notation "RawBank[" v "," h "," side "]" => Prod.fst
  (TriangleComplex.boundaryEndEquiv D (PotentialCutForest.retain Fcut) ParentBank[v,h,side])
local notation "Flag[" v "," h "," side "]" => Prod.snd
  (TriangleComplex.boundaryEndEquiv D (PotentialCutForest.retain Fcut) ParentBank[v,h,side])
local notation "PointAt[" v "," h "," side "," t "]" => TriangleComplex.bankParameterFromEnd D
  RawBank[v,h,side] Flag[v,h,side] t
local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W

/-- Every literal strict finite roof-bank mark has a whole occupied half-plane chart.
The model is the original face's supporting half-plane, and the original spatial
placement and center are retained. No supplied regularity certificate is needed. -/
theorem compatibleContourParentMark_halfPlane_chart
    (vertex : (D).Vertex Set.univ) (nonroot : vertex ∉ (Fcut).parents.roots)
    (side : Bool) (t : unitInterval) (bounds : 0 < t ∧ t < 1) :
    let bank := RawBank[vertex,nonroot,side]
    let q := PointAt[vertex,nonroot,side,t]
    let model := ((D).triangle bank.val.face).edgeHalfPlanePoint bank.val.edge q
    ∃ (r : ℝ) (positive_radius : 0 < r),
      ∃ A : Metric.eball ParentAt[vertex,nonroot,side,t] (ENNReal.ofReal r) ≃ᵢ
        Metric.ball model r,
        (A ⟨ParentAt[vertex,nonroot,side,t],
          Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive_radius)⟩).val = model ∧
        ∀ z, (T).placement bank.val.face (A z).val.val =
          (W.partition.restoreCut R.carrier z.val).val := by
  dsimp only
  let bank := RawBank[vertex,nonroot,side]
  let q := PointAt[vertex,nonroot,side,t]
  let source := (D).bankMap (Fcut).retain bank q
  let N := (D).boundaryChart (Fcut).retain bank q
    ((D).bankParameterFromEnd_nonvertex bank Flag[vertex,nonroot,side] t bounds.1 bounds.2)
  obtain ⟨δ, δpos, C, agrees_C⟩ := K.compatibleMesh_ball_chart_at compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W source
    (K.compatibleContourParentPath_height_lt compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts vertex nonroot side t bounds.2)
  let model := ((D).triangle bank.val.face).edgeHalfPlanePoint bank.val.edge q
  let place : ((D).triangle bank.val.face).edgeHalfPlane bank.val.edge → Space :=
    fun p => (T).placement bank.val.face p.val
  have injective : Function.Injective place :=
    ((T).placement bank.val.face).injective.comp Subtype.val_injective
  obtain ⟨r, positive_radius, A, physical⟩ := exists_restored_placed_ball_chart Map
    ((T).pairedFolding.toSpace (Fcut).retain)
    (fun x : W.Cut => (W.partition.restoreCut R.carrier x).val) place injective
    (K.restore_compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W) δpos N.positive C agrees_C N.halfPlaneChart
    ((T).pairedFolding.boundary_halfPlaneChart_physical N) (show place model =
      (T).pairedFolding.toSpace (Fcut).retain source from rfl)
  refine ⟨r, positive_radius, A, ?_, physical⟩
  apply injective
  have center := physical ⟨ParentAt[vertex,nonroot,side,t],
    Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive_radius)⟩
  exact center.trans (K.restore_compatibleMeshWholeMap compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W source)

/-- A physical whole roof-bank chart retains each nearby original finite parameter
in its literal original face coordinates, including closed endpoint parameters. -/
theorem compatibleContourParentMark_chart_parameter
    (vertex : (D).Vertex Set.univ) (nonroot : vertex ∉ (Fcut).parents.roots)
    (side : Bool) (t : unitInterval) {r : ℝ} :
    let bank := RawBank[vertex,nonroot,side]
    let q := PointAt[vertex,nonroot,side,t]
    let model := ((D).triangle bank.val.face).edgeHalfPlanePoint bank.val.edge q
    ∀ A : Metric.eball ParentAt[vertex,nonroot,side,t] (ENNReal.ofReal r) ≃ᵢ Metric.ball model r,
      (∀ z, (T).placement bank.val.face (A z).val.val =
        (W.partition.restoreCut R.carrier z.val).val) →
      ∀ (s : unitInterval)
        (near : ParentAt[vertex,nonroot,side,s] ∈
          Metric.eball ParentAt[vertex,nonroot,side,t] (ENNReal.ofReal r)),
        (A ⟨ParentAt[vertex,nonroot,side,s], near⟩).val.val =
          (PointAt[vertex,nonroot,side,s]).val := by
  dsimp only
  intro A physical s near
  apply ((T).placement (RawBank[vertex,nonroot,side]).val.face).injective
  exact (physical ⟨ParentAt[vertex,nonroot,side,s], near⟩).trans
    (K.restore_compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W PathAt[vertex,nonroot,side,s])

end Unfoldings.ConvexRoof
