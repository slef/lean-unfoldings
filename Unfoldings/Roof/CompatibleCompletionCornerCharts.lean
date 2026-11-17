module

public import Unfoldings.Roof.CompatibleProcessedCarrier
public import Unfoldings.Roof.CompatibleLevelWindow
public import Unfoldings.Roof.CompatibleProcessedMeshCharts
public import Unfoldings.Roof.CompatiblePartialWindowPairedCenters
public import Unfoldings.Roof.CompatibleProcessedCornerCharts
public import Unfoldings.Roof.CompletionOriginalConforming
public import Unfoldings.Roof.CompletionOriginalSpatial
public import Unfoldings.Metric.IsometricChartSource

/-! Physical completion fans in actual intermediate whole cuts. -/

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

local instance completedCornerChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance completedCornerChartWholeFintype : Fintype W.Index := W.finiteIndex

local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S
local notation "CutsAt[" S "]" => K.compatibleMeshProcessedCarrier compact nonempty R no_boundary
  level higher M positive inner_disk beta acute S
variable {φ : ℝ} {region : Set Plane}

local instance completedCornerFineFintype
    (E : (Q).CompletionMesh φ region (Q).originalEdgeEquations) : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- The physical original-face subdivision maps to its actual intermediate whole cut. -/
@[macro_inline] def compatibleMeshCompletedWholeMap
    (E : (Q).CompletionMesh φ region (Q).originalEdgeEquations) (S : (Fcut).parents.ParentFrontier)
    (y : E.originalComplex.Realization (E.originalRetain RetainAt[S])) :
    W.partition.Cut CutsAt[S] :=
  K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W S (E.originalMetricEquiv RetainAt[S] y)

open Classical in
/-- The completion inclusion keeps every actual original spatial point and cut-side copy. -/
theorem restore_compatibleMeshCompletedWholeMap
    (E : (Q).CompletionMesh φ region (Q).originalEdgeEquations) (S : (Fcut).parents.ParentFrontier)
    (y : E.originalComplex.Realization (E.originalRetain RetainAt[S])) :
    (W.partition.restoreCut CutsAt[S]
      (K.compatibleMeshCompletedWholeMap compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W E S y)).val =
      (E.partition.pairedFolding.restrictFaces E.originalPieceSet).toSpace
        (E.originalRetain RetainAt[S]) y :=
  (K.restore_compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W S (E.originalMetricEquiv RetainAt[S] y)).trans
      (E.originalMetricEquiv_toSpace RetainAt[S] y).symm

open Classical in
/-- A specified physical completion copy has its own whole original-cut neighborhood.
Only strict containment below truncation is needed; the actual metric inclusion is derived. -/
theorem compatibleMeshCompleted_ball_chart_at
    (E : (Q).CompletionMesh φ region (Q).originalEdgeEquations) (S : (Fcut).parents.ParentFrontier)
    (y : E.originalComplex.Realization (E.originalRetain RetainAt[S]))
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace RetainAt[S]
        (E.originalMetricEquiv RetainAt[S] y))) < level) :
    ∃ r : ℝ, 0 < r ∧ ∃ chart : Metric.eball y (ENNReal.ofReal r) ≃ᵢ
      Metric.eball
        (K.compatibleMeshCompletedWholeMap compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W E S y) (ENNReal.ofReal r), ∀ z, (chart z).val =
          K.compatibleMeshCompletedWholeMap compact nonempty R no_boundary level higher M positive
            inner_disk beta acute W E S z.val := by
  exact centered_ball_chart_source_isometry (E.originalMetricEquiv RetainAt[S])
    (K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W S) y
    (K.compatibleMeshProcessed_ball_chart_at compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W S _ below)

open Classical in
/-- The entire actual retained fine fan of a physical completion is a whole fan neighborhood
of the same original whole-cut copy, with every tagged fine face coordinate retained. -/
theorem compatibleMeshCompleted_corner_fan_chart
    (E : (Q).CompletionMesh φ region (Q).originalEdgeEquations) (S : (Fcut).parents.ParentFrontier)
    (vertex : E.originalComplex.Vertex (E.originalRetain RetainAt[S]))
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace RetainAt[S]
        (E.originalMetricEquiv RetainAt[S]
          (E.originalComplex.vertexPoint (E.originalRetain RetainAt[S]) vertex)))) < level) :
    ∃ r : ℝ, 0 < r ∧
      ∃ chart : Metric.eball (E.originalComplex.tangentOrigin (E.originalRetain RetainAt[S]) vertex)
        (ENNReal.ofReal r) ≃ᵢ
        Metric.eball
          (K.compatibleMeshCompletedWholeMap compact nonempty R no_boundary level higher M positive
            inner_disk beta acute W E S
            (E.originalComplex.vertexPoint (E.originalRetain RetainAt[S]) vertex))
          (ENNReal.ofReal r),
        ∀ (a : E.originalComplex.TangentTotal (E.originalRetain RetainAt[S]) vertex)
          (near : edist (E.originalComplex.tangentPoint (E.originalRetain RetainAt[S]) vertex a)
            (E.originalComplex.tangentOrigin (E.originalRetain RetainAt[S]) vertex) <
              ENNReal.ofReal r),
          (chart ⟨E.originalComplex.tangentPoint (E.originalRetain RetainAt[S]) vertex a,
            near⟩).val =
            K.compatibleMeshCompletedWholeMap compact nonempty R no_boundary level higher M positive
              inner_disk beta acute W E S
              (E.originalComplex.tangentSurfaceTag (E.originalRetain RetainAt[S]) vertex a) :=
  (E.partition.pairedFolding.restrictFaces E.originalPieceSet).exists_tangentChart_of_localMap
    (E.originalRetain RetainAt[S]) vertex
    (K.compatibleMeshCompletedWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W E S)
    (K.compatibleMeshCompleted_ball_chart_at compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W E S _ below)

end Unfoldings.ConvexRoof
