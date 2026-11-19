module

public import Unfoldings.Cone.DirectedIntervalChart
public import Unfoldings.Roof.CompatibleContourSourceOnlyLeaf
public import Unfoldings.Roof.CompatibleMeshCornerCharts

/-! The actual whole roof corner at a positive leaf, ordered by its two banks. -/

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

local instance contourLeafRoofChartFintype : Fintype (T).Index :=
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

local instance contourLeafRoofChartWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "Retain" => PotentialCutForest.retain Fcut
local notation "VertexAt[" w "]" => TriangleComplex.vertexPoint D Retain w
local notation "Height[" x "]" => SlopeEnvelope.height (K.clippedExtension slopes compact nonempty)
  (Cap.horizontal (SpatialFolding.toSpace
    (SpatialEnvelope.Triangulation.pairedFolding
      (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) Retain x))
local notation "BankAt[" e "," side "]" => TriangleComplex.contourParentBank D Selection contour
  (PotentialCutForest.boundary_roots Fcut) starts (Subtype.val e) (Subtype.property e) side

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "SourceOf[" e "]" => TriangleComplex.positiveContourVertex D Selection contour e
/-- The whole roof at a positive leaf has the complement of its own gap defect.
The exit bank is on the positive axis and the entrance bank is on the terminal ray. -/
theorem compatibleContourSourceOnlyLeaf_roof_sector_chart (event : Event)
    (nonroot : SourceOf[event] ∉ (Fcut).parents.roots)
    (childless : ∀ v ∉ (Fcut).parents.roots, (Fcut).parents.parent v ≠ SourceOf[event]) :
    let edge := (⟨SourceOf[event], nonroot⟩ :
      {w : (D).Vertex Set.univ // w ∉ (Fcut).parents.roots})
    let p := BankAt[edge,false]
    let q := BankAt[edge,true]
    let w := (D).boundaryEndVertex Retain p
    let θ := (D).totalAngle Retain w
    let x := Map VertexAt[w]
    θ + (D).interiorAngularDefect Set.univ SourceOf[event] = 2 * Real.pi ∧
    Base (.inl edge) false 0 = x ∧ Base (.inl edge) true 0 = x ∧
    ∃ r : ℝ, 0 < r ∧
      ∃ chart : Metric.eball x (ENNReal.ofReal r) ≃ᵢ
          Metric.eball (closedAngularSectorOrigin ((D).totalAngle_pos Retain w).le)
            (ENNReal.ofReal r),
        (∀ (t : unitInterval) (near : edist (Base (.inl edge) false t) x < ENNReal.ofReal r),
          (chart ⟨Base (.inl edge) false t, near⟩).val.val =
            (t.val * (D).boundaryBankLength p : ℝ)) ∧
        (∀ (t : unitInterval) (near : edist (Base (.inl edge) true t) x < ENNReal.ofReal r),
          (chart ⟨Base (.inl edge) true t, near⟩).val.val =
            (t.val * (D).boundaryBankLength q) • polarRay θ) := by
  dsimp only
  let edge := (⟨SourceOf[event], nonroot⟩ :
    {w : (D).Vertex Set.univ // w ∉ (Fcut).parents.roots})
  let p := BankAt[edge,false]
  let q := BankAt[edge,true]
  let w := (D).boundaryEndVertex Retain p
  obtain ⟨_, w', _, below, balance, endpoints⟩ :=
    K.compatibleContourSourceOnlyLeaf_roof_fan compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W event nonroot childless
  have end_at (side : Bool) : (D).boundaryEndVertex Retain BankAt[edge,side] = w' := by
    have classified :=
      (K.compatibleContourRoofVertex_eq_parentMark_iff compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W w' below edge side 0).mp
        (endpoints side)
    rcases classified with ⟨_, start⟩ | ⟨one, _⟩
    · exact start.symm
    · exact (zero_ne_one one).elim
  have same : w' = w := (end_at false).symm
  subst w'
  have mate : (D).boundaryMate Retain p = q :=
    ((D).exists_unique_other_boundaryEnd Retain p).unique ((D).boundaryMate_spec Retain p)
      ⟨((D).contourParentBank_distinct Selection contour (Fcut).boundary_roots starts
        edge.val nonroot).symm, end_at true⟩
  have small : (D).totalAngle Retain w < 2 * Real.pi := by
    have pos : 0 < (D).interiorAngularDefect Set.univ SourceOf[event] := event.property.2
    linarith
  have speeds (b : (D).BoundaryEnd Retain) (at_vertex : (D).boundaryEndVertex Retain b = w)
      (t : unitInterval) :
      ENNReal.ofReal (t.val * (D).boundaryBankLength b) =
        edist (Map ((D).directedBoundaryPath b t)) (Map VertexAt[w]) := by
    have start : (D).directedBoundaryPath b 0 = VertexAt[w] :=
      ((D).directedBoundaryPath_zero b).trans (congrArg ((D).vertexPoint Retain) at_vertex)
    calc
      _ = ENNReal.ofReal ((D).boundaryBankLength b) * edist t (0 : unitInterval) := by
        rw [mul_comm t.val, ENNReal.ofReal_mul ((D).boundaryBankLength_pos b).le, edist_dist]
        congr 1
        apply congrArg ENNReal.ofReal
        change t.val = dist t.val 0
        rw [Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]
      _ = _ :=
        (((T).pairedFolding.edist_directedBoundaryPath_eq_length b t 0).symm.trans
          (K.compatibleWholeMap_edist_bank compact nonempty R no_boundary level higher M
            positive inner_disk beta acute W b t 0).symm).trans
          (congrArg (fun z => edist (Map ((D).directedBoundaryPath b t)) (Map z)) start)
  obtain ⟨r, rpos, chart, first, last⟩ := (D).exists_directedIntervalChart Retain p Map small
    speeds (K.compatibleMesh_corner_fan_chart compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W w below)
  refine ⟨balance, endpoints false, endpoints true, r, rpos, chart, first, ?_⟩
  have finish := last
  rw [mate] at finish
  exact finish

end Unfoldings.ConvexRoof
