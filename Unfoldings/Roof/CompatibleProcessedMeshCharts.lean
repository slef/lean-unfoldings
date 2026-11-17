module

public import Unfoldings.Roof.CompatibleProcessedCarrier
public import Unfoldings.Roof.CompatibleLevelWindow
public import Unfoldings.Roof.CompatiblePartialWindowPairedMesh

/-! Construct whole original-bank neighborhoods at every actual intermediate processing stage. -/

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

local instance processedMeshChartIndexFintype : Fintype (T).Index :=
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

local instance processedMeshChartWholeFintype : Fintype W.Index := W.finiteIndex

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

/-- Include the actual current retained mesh into its complete intermediate whole-roof cut. -/
@[macro_inline] def compatibleMeshProcessedWholeMap (S : (Fcut).parents.ParentFrontier)
    (y : (T).pairedComplex.Realization RetainAt[S]) : W.partition.Cut CutsAt[S] :=
  (V).partialPairedMeshMap proper full (T).toTriangulation domain heights CutsAt[S] ClosedAt[S]
    IncludedAt[S] OutsideAt[S] W conforming RetainAt[S] RemovedAt[S] KeptAt[S] y

/-- Every original intermediate whole-cut copy strictly below the truncation has an actual
finite retained mesh chart containing a whole intrinsic ball, with its original bank copies. -/
theorem exists_compatibleMeshProcessed_ball_chart (S : (Fcut).parents.ParentFrontier)
    (x : W.partition.Cut CutsAt[S])
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut CutsAt[S] x).val) < level) :
    ∃ source : (T).pairedComplex.Realization RetainAt[S],
      K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W S source = x ∧
      ∃ r : ℝ, 0 < r ∧ ∃ chart : Metric.eball source (ENNReal.ofReal r) ≃ᵢ
        Metric.eball x (ENNReal.ofReal r), ∀ z, (chart z).val =
          K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M positive
            inner_disk beta acute W S z.val := by
  apply (V).exists_partialPairedMesh_ball_chart proper full (T).toTriangulation domain heights
    CutsAt[S] ClosedAt[S] IncludedAt[S] OutsideAt[S] W conforming RetainAt[S] RemovedAt[S]
      KeptAt[S] x
  apply SpatialEnvelope.levelEquation_positive
  rw [M.height_eq]
  linarith

/-- The actual current-to-whole map retains the original spatial bank point. -/
theorem restore_compatibleMeshProcessedWholeMap (S : (Fcut).parents.ParentFrontier)
    (y : (T).pairedComplex.Realization RetainAt[S]) :
    (W.partition.restoreCut CutsAt[S]
      (K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W S y)).val = (T).pairedFolding.toSpace RetainAt[S] y :=
  (V).restore_partialPairedMeshMap proper full (T).toTriangulation domain heights CutsAt[S]
    ClosedAt[S] IncludedAt[S] OutsideAt[S] W conforming RetainAt[S] RemovedAt[S] KeptAt[S] y

/-- Current original mesh inclusions in their whole cut metrics are nonexpanding. -/
theorem compatibleMeshProcessedWholeMap_lipschitz (S : (Fcut).parents.ParentFrontier) :
    LipschitzWith 1 (K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S) :=
  (V).partialPairedMeshMap_lipschitz proper full (T).toTriangulation domain heights CutsAt[S]
    ClosedAt[S] IncludedAt[S] OutsideAt[S] W conforming RetainAt[S] RemovedAt[S] KeptAt[S]

end Unfoldings.ConvexRoof
