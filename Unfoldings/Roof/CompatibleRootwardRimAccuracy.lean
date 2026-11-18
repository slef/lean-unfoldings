module

public import Unfoldings.Roof.CompatibleRootwardRimRolling
public import Unfoldings.Roof.UniformRadialBankRolling

/-! Complete source-to-rim chains carry uniform physical comparisons and actual radial rolling
  data. -/

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

local instance rootwardRimAccuracyChainChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardRimAccuracyChainChartWholeFintype : Fintype W.Index := W.finiteIndex

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
local notation "PathAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshCurrentRootwardPath compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side j h k hk
local notation "HistoryAt[" j "," k "]" =>
  K.compatibleMeshHistory compact nonempty R no_boundary level higher M
    positive inner_disk beta acute SourceAt[j] (k + 2)
local notation "RootAt[" s "," h "]" =>
  K.compatibleMeshTerminalRoot compact nonempty R no_boundary level higher M
    positive inner_disk beta acute s h

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

local notation "ImageAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W FrontierAt[j]
    (K.compatibleMeshCurrentRootwardEnd compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side j h k hk)

local notation "NewAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh compact nonempty R no_boundary level higher M positive
    inner_disk beta acute S L h
local notation "NewRetainAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.retainOutside
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]

open Classical in
local instance rootwardRimAccuracyChainNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

local notation "JunctionAt[" j "," h "," k "," hk "," L "," hl "]" =>
  K.compatibleMeshCurrentRootwardComparisonJunction compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W r side j h k hk L hl
local notation "PairsAt[" S "," L "]" => K.compatibleMeshProcessedWindowPairs compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S L

local notation "StemAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshCurrentRootwardIntrinsicPath compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W r side j h k hk
local notation "MapAt[" S "]" => K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute W S

local notation "LiftAt[" S "," L "," h "," p "]" =>
  K.compatibleMeshProcessedComparisonFiniteBank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h p
local notation "NewMapAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h

variable {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b) (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
  (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2)

include bpos ratio upper small

local notation "ConformingAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh_conforming compact nonempty R no_boundary level higher
    M positive inner_disk beta acute S L h
local notation "HigherAt[" _L "," h "]" => fun v => lt_trans (higher v) h
local notation "NewRoofAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h])
  ConformingAt[S,L,h]
  (K.compatible_section_interior compact nonempty R L HigherAt[L,h] M)

open Classical in
/-- Uniform small-loss control of one actual rootward bank through any later rim. -/
theorem exists_uniform_compatibleRootward_rim_accuracy {ε : ℝ} (error_positive : 0 < ε)
    (error_small : ε < 1) :
    ∃ η > 0, ∃ χ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ ψ ∈ Set.Ioc (0 : ℝ) θ,
      (3 : ℝ) / 4 ≤ Real.cos ψ ∧
      radialBlockError (Real.cos ψ)⁻¹ η
        (Real.cos (2 * annularHistoryAngle (a / b) β))⁻¹
        (Real.sqrt (1 - (Real.cos (2 * annularHistoryAngle (a / b) β)) ^ 2)) (Real.pi / 4) < ε ∧
      ∀ (_normal : ∀ f, Real.cos ψ ≤ (M.plane f).normal 2),
      ∀ (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
        (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
        (later : ℝ) (ordered : level < later),
        let root := RootAt[SourceAt[i],by omega]
        let duration := R.terminalTime later root - R.terminalTime level root
        ∃ n : ℕ, ∃ full : ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundarySystem
            NewRetainAt[FrontierAt[i],later,ordered]).Chain n,
          (NewAt[FrontierAt[i],later,ordered]).pairedComplex.vertexPoint
            NewRetainAt[FrontierAt[i],later,ordered]
            ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryEndVertex
              NewRetainAt[FrontierAt[i],later,ordered] full.first) =
            LiftAt[FrontierAt[i],later,ordered,(ChainAt[i,fresh,m,length]).first] 0 ∧
          (NewAt[FrontierAt[i],later,ordered]).pairedFolding.boundaryPosition
            ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryTurn
              NewRetainAt[FrontierAt[i],later,ordered] full.last) =
            SpatialEnvelope.point M.plane (R.terminalPoint later root) ∧
          Set.range ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.projectedBoundaryChain
            full).path = Set.range (PathAt[i,fresh,m,length]).path ∪
              Set.range (fun u : Set.Icc (0 : ℝ) duration =>
                R.exterior.ray (R.terminalIndex root) (R.terminalTime level root + u.val)) ∧
          (NewRoofAt[FrontierAt[i],later,ordered]).RadialBankComparisons χ η
            (Real.cos (2 * annularHistoryAngle (a / b) β))
            NewRetainAt[FrontierAt[i],later,ordered] full ((Q).projectedVertex SourceAt[i]) ∧
          (NewRoofAt[FrontierAt[i],later,ordered]).BankRollAccuracy ε
            ((Real.cos ψ)⁻¹ * (Real.cos (2 * annularHistoryAngle (a / b) β))⁻¹ / (1 - ε))
            NewRetainAt[FrontierAt[i],later,ordered] full := by
  have gamma_positive := fine_annular_radial_margin_pos small
  obtain ⟨η, eta_positive, χ, chi_bounds, θ, theta_bounds, uniform⟩ :=
    SpatialEnvelope.Triangulation.exists_uniform_radial_bank_rolling.{0}
      error_positive error_small gamma_positive (Real.cos_le_one _)
  refine ⟨η, eta_positive, χ, chi_bounds, θ, theta_bounds, ?_⟩
  intro ψ psi_bounds
  obtain ⟨cos_lower, small_error, accurate⟩ := uniform ψ psi_bounds
  refine ⟨cos_lower, small_error, ?_⟩
  intro normal i fresh m length later ordered
  dsimp only
  obtain ⟨tailSide, D, n, full, first, _last, final, starts, margin, radial, initial, carrier⟩ :=
    K.exists_compatibleMeshCurrentRootwardComparisonRimRadialChain compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W r side bpos ratio upper small
      i fresh m length later ordered
  let P := (NewAt[FrontierAt[i],later,ordered]).pairedFolding.projectedBoundaryChain full
  let source := (Q).projectedVertex SourceAt[i]
  have domain (j) : Cap.horizontal
      ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.boundaryPosition (full.point j)) ∈
        interior (SpatialEnvelope.clip M.plane (-later)) := by
    rw [M.clip_eq_sublevel, neg_neg]
    exact (K.clippedExtension slopes compact nonempty).mem_interior_sublevel (starts j)
  have physical_margin (j) : Real.cos (2 * annularHistoryAngle (a / b) β) *
      (‖P.vertex j.castSucc - source‖ * ‖P.edge j‖) ≤
      inner ℝ (P.vertex j.castSucc - source) (P.edge j) := by
    rw [SpatialFolding.projectedBoundaryChain_vertex_castSucc,
      SpatialFolding.projectedBoundaryChain_edge]
    exact margin j
  obtain ⟨data, estimate⟩ := accurate M.plane
    (NewAt[FrontierAt[i],later,ordered]).toTriangulation
    ConformingAt[FrontierAt[i],later,ordered]
    (K.compatible_section_interior compact nonempty R later HigherAt[later,ordered] M)
    normal NewRetainAt[FrontierAt[i],later,ordered] full source radial initial domain
    physical_margin
  exact ⟨n, full, first, final, carrier, data, estimate⟩

end Unfoldings.ConvexRoof
