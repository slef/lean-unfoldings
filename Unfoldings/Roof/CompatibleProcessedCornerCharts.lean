module

public import Unfoldings.Roof.CompatibleProcessedCarrier
public import Unfoldings.Roof.CompatibleLevelWindow
public import Unfoldings.Roof.CompatibleProcessedMeshCharts
public import Unfoldings.Roof.CompatiblePartialWindowPairedCenters
public import Unfoldings.Cone.TransportedCharts

/-! Whole current-cut fan charts at specified original corner copies. -/

@[expose] public section

noncomputable section

open scoped ENNReal

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

local instance processedCornerChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "B" => SlopeEnvelope.boundaryEnvelope
  (K.clippedExtension slopes compact nonempty) boundary
local notation "Gcut" => K.truncatedCutEmbedding compact nonempty R no_boundary level higher


local notation "V" => R.levelWindowModel M level higher
local notation "proper" => R.levelWindow_proper M level higher
local notation "full" => R.levelWindow_full M level higher
local notation "domain" => SpatialEnvelope.levelEquation_domain M.plane (-level)
local notation "heights" => (Set.eqOn_refl (SpatialEnvelope.height M.plane) _)
local notation "outside" => K.compatibleMesh_cut_disjoint_interior compact nonempty R
  no_boundary level higher M positive inner_disk
variable (W : R.WholeCutModel M)

local instance processedCornerChartWholeFintype : Fintype W.Index := W.finiteIndex

local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S
local notation "CutsAt[" S "]" => K.compatibleMeshProcessedCarrier compact nonempty R no_boundary
  level higher M positive inner_disk beta acute S
local notation "ClosedAt[" S "]" => K.isClosed_compatibleMeshProcessedCarrier compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "IncludedAt[" S "]" => K.compatibleMeshProcessedCarrier_subset compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "OutsideAt[" S "]" =>
  fun f => Disjoint.mono_right IncludedAt[S]
    (K.compatibleMesh_cut_disjoint_interior compact nonempty R no_boundary level higher M positive
      inner_disk f)
local notation "RemovedAt[" S "]" => K.compatibleMeshProcessed_removed_edge compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "KeptAt[" S "]" => K.compatibleMeshProcessed_retained_open_edge compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S

/-- A specified current finite cut copy retains its own whole original-cut neighborhood.
The center is the selected intrinsic copy, including at cut vertices. -/
theorem compatibleMeshProcessed_ball_chart_at (S : (Fcut).parents.ParentFrontier)
    (y : (T).pairedComplex.Realization RetainAt[S])
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace RetainAt[S] y)) < level) :
    ∃ r : ℝ, 0 < r ∧ ∃ chart : Metric.eball y (ENNReal.ofReal r) ≃ᵢ
      Metric.eball
        (K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W S y) (ENNReal.ofReal r), ∀ z, (chart z).val =
          K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M positive
            inner_disk beta acute W S z.val := by
  apply (V).partialPairedMesh_ball_chart_at proper full (T).toTriangulation domain heights
    CutsAt[S] ClosedAt[S] IncludedAt[S] OutsideAt[S] W conforming RetainAt[S] RemovedAt[S]
    KeptAt[S] y
  apply SpatialEnvelope.levelEquation_positive
  rw [M.height_eq]
  linarith

/-- Every original retained corner of an intermediate cut has its complete actual tangent
fan in the whole cut. Every tagged face coordinate and its intrinsic vertex copy are retained. -/
theorem compatibleMeshProcessed_corner_fan_chart (S : (Fcut).parents.ParentFrontier)
    (vertex : (T).pairedComplex.Vertex RetainAt[S])
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace RetainAt[S]
        ((T).pairedComplex.vertexPoint RetainAt[S] vertex))) < level) :
    ∃ r : ℝ, 0 < r ∧
      ∃ chart : Metric.eball ((T).pairedComplex.tangentOrigin RetainAt[S] vertex)
        (ENNReal.ofReal r) ≃ᵢ
        Metric.eball
          (K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M positive
            inner_disk beta acute W S ((T).pairedComplex.vertexPoint RetainAt[S] vertex))
          (ENNReal.ofReal r),
        ∀ (a : (T).pairedComplex.TangentTotal RetainAt[S] vertex)
          (near : edist ((T).pairedComplex.tangentPoint RetainAt[S] vertex a)
            ((T).pairedComplex.tangentOrigin RetainAt[S] vertex) < ENNReal.ofReal r),
          (chart ⟨(T).pairedComplex.tangentPoint RetainAt[S] vertex a, near⟩).val =
            K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M positive
              inner_disk beta acute W S
              ((T).pairedComplex.tangentSurfaceTag RetainAt[S] vertex a) :=
  (T).pairedFolding.exists_tangentChart_of_localMap RetainAt[S] vertex
    (K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W S)
    (K.compatibleMeshProcessed_ball_chart_at compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W S _ below)

end Unfoldings.ConvexRoof
