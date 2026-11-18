module

public import Unfoldings.Roof.CompatibleContourGraft
public import Unfoldings.Roof.CompatibleFreshSourceGapGeometry

/-! One tilt constructs a complete graft from the actual canonical positive-side gap regions. -/

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

local instance canonicalContourGraftIndexFintype : Fintype (T).Index :=
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


local instance canonicalContourGraftWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W

/-- The canonical occupied side, both radial banks and every original opening are derived
uniformly for the entire actual positive contour-source family. -/
theorem exists_uniform_contour_gap_geometry {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
    (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
    (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ ψ ∈ Set.Ioc (0 : ℝ) θ,
      (∀ i, Real.cos ψ ≤ (M.plane i).normal 2) →
      ∀ (contour : (T).pairedComplex.BoundaryContour
          ((T).pairedComplex.selectedRetain (Fcut).selection))
        (starts : SourceAt[contour,0] ∈ (Fcut).parents.roots)
        (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour),
        OrientedBankGap BankAt[contour,starts,event] OpenedAt[contour,starts,event] := by
  obtain ⟨θ, bounds, geometry⟩ := K.exists_uniform_freshSource_gap_geometry compact nonempty R
    no_boundary level higher M positive inner_disk beta acute bpos ratio upper small
  refine ⟨θ, bounds, ?_⟩
  intro ψ psi_bounds normal contour starts event
  exact geometry ψ psi_bounds normal contour starts event.val event.property.1
    LengthAt[contour,event] SpanAt[contour,event] event.property.2

/-- Complete bank gluing of the original roof and the canonical occupied positive-source gaps.
Its actual finite/infinite bank matches are proved by the general contour-graft API. -/
abbrev compatibleCanonicalContourGraft
    (geometry : ∀ event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour,
      OrientedBankGap BankAt[contour,starts,event] OpenedAt[contour,starts,event]) :=
  K.compatibleContourGraft compact nonempty R no_boundary level higher M positive inner_disk
    beta acute contour starts W (fun event => (geometry event).model)

end Unfoldings.ConvexRoof
