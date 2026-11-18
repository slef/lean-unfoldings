module

public import Unfoldings.Roof.CompatibleFreshSourceGap
public import Unfoldings.Complex.ContourGapBankIndex
public import Unfoldings.Geometry.BankGapModel

/-! One tilt constructs all actual positive contour gaps with concrete cells. -/

@[expose] public section

noncomputable section

open scoped NNReal

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

local instance compatibleContourGapModelIndexFintype : Fintype (T).Index :=
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

/-- Every positive contour source determines its actual complete reference bank without
an externally chosen length, path, source match or terminal direction. -/
def compatibleContourSourceBank
    (contour : (T).pairedComplex.BoundaryContour
      ((T).pairedComplex.selectedRetain (Fcut).selection))
    (starts : SourceAt[contour,0] ∈ (Fcut).parents.roots)
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour) :
    PolygonalRay ℂ (LengthAt[contour,event] + 1) :=
  ((T).pairedComplex.boundaryChainRoll
    ChainAt[contour,starts,event.val,event.property.1,LengthAt[contour,event],
      SpanAt[contour,event]]).terminalEdgeRay

local notation "BankAt[" q "," h "," e "]" =>
  K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e
/-- The canonical opened bank remembers every original hinge and the true infinite tail. -/
def compatibleContourOpenedBank
    (contour : (T).pairedComplex.BoundaryContour
      ((T).pairedComplex.selectedRetain (Fcut).selection))
    (starts : SourceAt[contour,0] ∈ (Fcut).parents.roots)
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour) :
    PolygonalRay ℂ (LengthAt[contour,event] + 1) :=
  (BankAt[contour,starts,event]).openings
    (PolygonalChain.castOpenings SpanAt[contour,event]
      ((T).pairedComplex.contourRootwardOpenings (Fcut).selection contour event.val.succ
        VertexAt[contour,event]))

local notation "OpenedAt[" q "," h "," e "]" =>
  K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e

/-- A single tilt constructs all positive source gaps simultaneously in their actual source
order. Every model has its intrinsic metric, concrete finite convex cells and named bank marks. -/
theorem exists_uniform_contourGapModels {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
    (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
    (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ ψ ∈ Set.Ioc (0 : ℝ) θ,
      (∀ i, Real.cos ψ ≤ (M.plane i).normal 2) →
      ∀ (contour : (T).pairedComplex.BoundaryContour
          ((T).pairedComplex.selectedRetain (Fcut).selection))
        (starts : SourceAt[contour,0] ∈ (Fcut).parents.roots),
        Nonempty (∀ event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour,
          BankGapModel BankAt[contour,starts,event] OpenedAt[contour,starts,event]) := by
  obtain ⟨θ, bounds, gaps⟩ := K.exists_uniform_freshSource_opening_gap compact nonempty R
    no_boundary
    level higher M positive inner_disk beta acute bpos ratio upper small
  refine ⟨θ, bounds, ?_⟩
  intro ψ psi_bounds normal contour starts
  have each (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour) :
      Nonempty (BankGapModel BankAt[contour,starts,event] OpenedAt[contour,starts,event]) := by
    obtain ⟨region, closed, frontier_eq, banks_meet, nonempty_region, regular_closed, complete,
      contractible, Cell, finite, cells, geometry, disjoint, cover⟩ :=
      gaps ψ psi_bounds normal contour starts event.val event.property.1 LengthAt[contour,event]
        SpanAt[contour,event] event.property.2
    exact ⟨{
      region := region
      closed := closed
      frontier_eq := frontier_eq
      banks_meet := banks_meet
      interior_nonempty := nonempty_region
      regular_closed := regular_closed
      complete := complete
      contractible := contractible
      Cell := Cell
      finite := finite
      cells := cells
      cell_closed := fun i => (geometry i).1
      cell_convex := fun i => (geometry i).2.1
      cell_interior := fun i => (geometry i).2.2
      cell_disjoint := disjoint
      cover := cover }⟩
  exact ⟨fun event => Classical.choice (each event)⟩

end Unfoldings.ConvexRoof
