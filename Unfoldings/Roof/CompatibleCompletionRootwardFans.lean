module

public import Unfoldings.Roof.CompatibleRootwardTerminalJoin
public import Unfoldings.Roof.CompatibleProcessedTerminalBanks
public import Unfoldings.Complex.BoundaryChainPath
public import Unfoldings.Roof.CompatibleCompletionCornerCharts
public import Unfoldings.Roof.SupportedCompletionRootwardChain
public import Unfoldings.Roof.CompletionChainTrace
public import Unfoldings.Roof.CompatibleMeshRetention

/-! Physical rootward refinements retain actual whole-cut fans, not just angle values. -/

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

local instance completedRootwardIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance completedRootwardWholeFintype : Fintype W.Index := W.finiteIndex

variable (r : {v // v ∈ R.parents.roots}) (side : Bool)

local notation "contour" => K.compatibleMeshRimContour compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W r side

local notation "SourceAt[" j "]" => TriangleComplex.contourOriginalVertex
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) contour j
local notation "FrontierAt[" j "]" => TriangleComplex.contourFrontier
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) contour j
local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S
local notation "CutsAt[" S "]" => K.compatibleMeshProcessedCarrier compact nonempty R no_boundary
  level higher M positive inner_disk beta acute S
local notation "IncludedAt[" S "]" => K.compatibleMeshProcessedCarrier_subset compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "ChainAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshCurrentRootwardChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side j h k hk

local notation "MapAt[" j "]" => K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute W FrontierAt[j]
/-- Every used fine parent starts strictly below truncation. Unused marked roots cause
no extra hypothesis: this concerns precisely the original selected nonroot vertices. -/
theorem compatibleMesh_nonroot_height_lt
    (v : (T).pairedComplex.Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots) :
    (K.clippedExtension slopes compact nonempty).height ((Q).projectedVertex v) < level := by
  let e : {v // v ∉ (Fcut).parents.roots} := ⟨v, nonroot⟩
  have selected := (Fcut).selected_subset e
  rw [(T).toTriangulation.roof_projectedTriangle conforming inside] at selected
  have increasing := (Fcut).parents.ascending v nonroot
  rw [(Fcut).height_eq] at increasing
  obtain ⟨path⟩ := K.compatibleMesh_oriented_seam compact nonempty R no_boundary level higher
    positive inner_disk beta acute M ((Fcut).selection.link e) selected increasing
  exact K.oriented_truncated_start_strict compact nonempty R no_boundary level higher path

/-- Every starting corner of the actual surviving stem is strictly below truncation.
The final rim endpoint is deliberately excluded from this finite-fan statement. -/
theorem compatibleMeshCurrentRootwardChain_corner_height_lt
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) (j : Fin (m + 1)) :
    (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace RetainAt[FrontierAt[i]]
        ((T).pairedComplex.vertexPoint RetainAt[FrontierAt[i]]
          ((T).pairedComplex.boundaryEndVertex RetainAt[FrontierAt[i]]
            ((ChainAt[i,fresh,m,length]).point j))))) < level := by
  rw [← (T).toTriangulation.roof_projectedVertex_vertexForgetCuts conforming inside
    RetainAt[FrontierAt[i]]]
  rw [K.compatibleMeshCurrentRootwardChain_original]
  apply K.compatibleMesh_nonroot_height_lt compact nonempty R no_boundary level higher M
    positive inner_disk beta acute
  apply (Fcut).parents.iterate_lt_distanceToRoot_not_mem
  omega

variable {φ : ℝ} {region : Set Plane}

local instance completedRootwardFineFintype
    (E : (Q).CompletionMesh φ region (Q).originalEdgeEquations) : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- Construct the physical refinement of the actual current rootward bank in a completion. -/
@[macro_inline] def compatibleMeshCompletedRootwardRefinement
    (E : (Q).CompletionMesh φ region (Q).originalEdgeEquations)
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    E.OriginalChainRefinement RetainAt[FrontierAt[i]] (ChainAt[i,fresh,m,length]) :=
  E.rootwardChainRefinement_of_boundary_roots (Fcut).selection (Fcut).boundary_roots contour
    (K.compatibleMeshRimContour_starts_root compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side) i
    (K.compatibleMeshRimContour_fresh_contactTime compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side i fresh) m length

local notation "RefinedAt[" e "," j "," h "," k "," hk "]" =>
  K.compatibleMeshCompletedRootwardRefinement compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side e j h k hk

open Classical in
/-- The whole physical fine-bank trace is exactly the actual original whole-cut stem,
including its original endpoint copies. No spatial coincidence is substituted for equality. -/
theorem compatibleMeshCompletedRootwardRefinement_whole_trace
    (E : (Q).CompletionMesh φ region (Q).originalEdgeEquations)
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    (K.compatibleMeshCompletedWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W E FrontierAt[i]) ''
        E.originalComplex.boundaryChainTrace (RefinedAt[E,i,fresh,m,length]).chain =
      MapAt[i] '' (T).pairedComplex.boundaryChainTrace (ChainAt[i,fresh,m,length]) :=
  (RefinedAt[E,i,fresh,m,length]).observed_trace_image MapAt[i]

open Classical in
/-- Original starting hinges keep their full unreduced one-sided angle in the physical
completion; the index identifies the actual original intrinsic copy. -/
theorem compatibleMeshCompletedRootwardRefinement_old_angle
    (E : (Q).CompletionMesh φ region (Q).originalEdgeEquations)
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) (j : Fin (m + 1)) :
    let fine := RefinedAt[E,i,fresh,m,length]
    E.originalComplex.totalAngle (E.originalRetain RetainAt[FrontierAt[i]])
      (E.originalComplex.boundaryEndVertex (E.originalRetain RetainAt[FrontierAt[i]])
        (fine.chain.point (fine.coarseIndex j))) =
      (T).pairedComplex.totalAngle RetainAt[FrontierAt[i]]
        ((T).pairedComplex.boundaryEndVertex RetainAt[FrontierAt[i]]
          ((ChainAt[i,fresh,m,length]).point j)) :=
  (RefinedAt[E,i,fresh,m,length]).coarseIndex_totalAngle j

open Classical in
/-- Every additional subdivision hinge is straight. Only the original hinges turn the roll. -/
theorem compatibleMeshCompletedRootwardRefinement_new_angle
    (E : (Q).CompletionMesh φ region (Q).originalEdgeEquations)
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    (j : Fin ((RefinedAt[E,i,fresh,m,length]).length + 1))
    (new : ∀ k, (RefinedAt[E,i,fresh,m,length]).coarseIndex k ≠ j) :
    E.originalComplex.totalAngle (E.originalRetain RetainAt[FrontierAt[i]])
      (E.originalComplex.boundaryEndVertex (E.originalRetain RetainAt[FrontierAt[i]])
        ((RefinedAt[E,i,fresh,m,length]).chain.point j)) = Real.pi :=
  (RefinedAt[E,i,fresh,m,length]).totalAngle_eq_pi_of_new j new

open Classical in
/-- Every original stem hinge in the actual completion carries its whole original intrinsic
fan into the intermediate whole cut. Strict containment and all fan identifications are derived
from the selected rootward path; no local-metric or fan matching certificate is supplied. -/
theorem compatibleMeshCompletedRootwardRefinement_old_fan_chart
    (E : (Q).CompletionMesh φ region (Q).originalEdgeEquations)
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) (j : Fin (m + 1)) :
    let fine := RefinedAt[E,i,fresh,m,length]
    let retain := E.originalRetain RetainAt[FrontierAt[i]]
    let vertex := E.originalComplex.boundaryEndVertex retain
      (fine.chain.point (fine.coarseIndex j))
    ∃ radius : ℝ, 0 < radius ∧
      ∃ chart : Metric.eball (E.originalComplex.tangentOrigin retain vertex)
          (ENNReal.ofReal radius) ≃ᵢ
        Metric.eball
          (K.compatibleMeshCompletedWholeMap compact nonempty R no_boundary level higher M positive
            inner_disk beta acute W E FrontierAt[i]
            (E.originalComplex.vertexPoint retain vertex)) (ENNReal.ofReal radius),
        ∀ (a : E.originalComplex.TangentTotal retain vertex)
          (near : edist (E.originalComplex.tangentPoint retain vertex a)
            (E.originalComplex.tangentOrigin retain vertex) < ENNReal.ofReal radius),
          (chart ⟨E.originalComplex.tangentPoint retain vertex a, near⟩).val =
            K.compatibleMeshCompletedWholeMap compact nonempty R no_boundary level higher M positive
              inner_disk beta acute W E FrontierAt[i]
              (E.originalComplex.tangentSurfaceTag retain vertex a) := by
  dsimp only
  apply K.compatibleMeshCompleted_corner_fan_chart compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W E FrontierAt[i]
  rw [(RefinedAt[E,i,fresh,m,length]).coarseIndex_image]
  exact K.compatibleMeshCurrentRootwardChain_corner_height_lt compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W r side i fresh m length j

end Unfoldings.ConvexRoof
