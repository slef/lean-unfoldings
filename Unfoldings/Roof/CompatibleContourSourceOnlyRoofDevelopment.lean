module

public import Unfoldings.Roof.CompatibleContourSourceOnlyGraftDevelopment
public import Unfoldings.Roof.CompatibleContourSourceOnlyGaps

/-! Nonoverlapping development of the retained roof cells in the source-only graft. -/

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

local instance sourceOnlyRoofDevelopmentIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
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
  (geometry : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    OrientedBankGap
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance sourceOnlyRoofDevelopmentWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "models" => (fun event : Event => OrientedBankGap.model (geometry event))
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Pieces" => polygonalBankStackPiece W.Cut
  (fun event : Event => BankGapModel.region (models event))
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "Gap" => K.compatibleContourSourceOnlyGapMark compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts models

local notation "LengthAt[" e "]" => TriangleComplex.positiveContourBankLength D Selection contour e
local notation "BankAt[" e "]" => K.compatibleContourSourceBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "Index" => K.compatibleContourSourceOnlyCellIndex compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "Cells" => K.compatibleContourSourceOnlyCells compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts W models
local notation "Raw" => MetricGluing.NestedCell (fun i j => Cells i j)
local notation "Seams" => K.compatibleContourSourceOnlyClosedSeams compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

local notation "Graft" => K.compatibleContourSourceOnlyGraft compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "L" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Rgt" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams L Rgt

local notation "Point" => MetricGluing.point Pieces Banks
local notation "Visit[" j "]" => TriangleComplex.contourOriginalVertex D Selection contour j

include geometry

set_option maxHeartbeats 3600000 in
-- The surviving roof cells are the original none-tag summand of the finite graft presentation.
/-- Restrict the global development to the original cut roof. Each original
cell is moved rigidly, the preserved adjacencies agree, and the developed
interiors of distinct cells are disjoint. -/
theorem compatibleContourSourceOnlyGraft_exists_nonoverlapping_roof_development
    (convex : Convex ℝ slopes) (ends : Visit[Fin.last contour.length] ∈ (Fcut).parents.roots)
    (strict : ∀ (e : Event) (k : Fin LengthAt[e]), let B := BankAt[e]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ)) :
    ∃ (develop : W.Cut → Plane) (place : W.Index → Plane ≃ᵃⁱ[ℝ] Plane),
      Continuous develop ∧
      (∀ i (x : W.partition.planarCell i), place i x.val = develop
        (MetricGluing.of (fun j => W.partition.planarCell j)
            (W.partition.cutGlue R.carrier) i x)) ∧
      Pairwise (fun i j =>
        Disjoint (place i '' interior (W.partition.planarCell i))
          (place j '' interior (W.partition.planarCell j))) := by
  obtain ⟨develop, preserves, onto⟩ := K.compatibleContourSourceOnlyGraft_exists_surjective_isometry
    compact nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W
    geometry convex ends strict
  let E := K.compatibleContourSourceOnlyClosedSeamsIsometry compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models
  let A : Graft ≃ᵢ Plane :=
    { toEquiv := Equiv.ofBijective develop ⟨preserves.injective, onto⟩
      isometry_toFun := preserves }
  let B := E.trans A
  let : PreconnectedSpace (MetricGluing.Realization Raw (Seams).relation) :=
    B.symm.surjective.denseRange.preconnectedSpace B.symm.continuous
  have shape (ij : Σ i, Index i) :=
    K.compatibleContourSourceOnlyCells_geometry compact nonempty R no_boundary level higher
      M positive inner_disk beta acute contour starts W models ij.1 ij.2
  obtain ⟨placements, agrees, apart⟩ := MetricGluing.exists_cell_placements_of_isometry
    (fun ij : Σ i, Index i => Cells ij.1 ij.2) (Seams).relation (develop ∘ E)
    (preserves.comp E.isometry) (fun ij => (shape ij).2.1) (fun ij => (shape ij).2.2)
    (K.compatibleContourSourceOnlyClosedSeams_boundary compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W models)
  let place (i : W.Index) := placements ⟨none, i⟩
  let layout (x : W.Cut) := develop (Point ⟨none, x⟩)
  have cont : Continuous layout :=
    preserves.continuous.comp (MetricGluing.of_lipschitz Pieces Banks none).continuous
  refine ⟨layout, place, cont, ?_, ?_⟩
  · intro i x
    exact agrees ⟨none, i⟩ x
  · intro i j different
    exact apart (fun same => different (eq_of_heq (Sigma.mk.inj same).2))

omit geometry
include no_boundary level higher positive inner_disk

set_option maxHeartbeats 2200000 in
-- Construct the original complete contour and its compatible gap geometry at the uniform tilt.
/-- Under the annular history-angle bound, the small-tilt compatible roof has
a nonoverlapping rigid development of the original cut cells. -/
theorem exists_uniform_compatibleRoof_nonoverlapping_development
    (convex : Convex ℝ slopes) {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
    (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
    (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ ψ ∈ Set.Ioc (0 : ℝ) θ,
      (∀ i, Real.cos ψ ≤ (M.plane i).normal 2) →
      ∃ (develop : W.Cut → Plane) (place : W.Index → Plane ≃ᵃⁱ[ℝ] Plane),
        Continuous develop ∧
        (∀ i (x : W.partition.planarCell i), place i x.val = develop
          (MetricGluing.of (fun j => W.partition.planarCell j) (W.partition.cutGlue R.carrier) i x)) ∧
        Pairwise (fun i j =>
          Disjoint (place i '' interior (W.partition.planarCell i))
            (place j '' interior (W.partition.planarCell j))) := by
  obtain ⟨θ, tilt, chosen⟩ := K.exists_uniform_contourSourceOnlyGap_geometry compact nonempty R
    no_boundary level higher M positive inner_disk beta acute bpos ratio upper small
  obtain ⟨q, q_start, q_end, _⟩ := K.exists_compatibleMesh_completeSourceContour
    compact nonempty R no_boundary level higher positive inner_disk beta acute M convex
  refine ⟨θ, tilt, fun ψ hψ normal => ?_⟩
  let modelsAt e := chosen ψ hψ normal q q_start e
  exact K.compatibleContourSourceOnlyGraft_exists_nonoverlapping_roof_development compact
    nonempty R no_boundary level higher M positive inner_disk beta acute q q_start W
    (fun e => (modelsAt e).1) convex q_end (fun e k => ((modelsAt e).2 k).1)

end Unfoldings.ConvexRoof
