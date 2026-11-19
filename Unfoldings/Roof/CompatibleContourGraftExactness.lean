module

public import Unfoldings.Roof.CompatibleContourFiniteClasses
public import Unfoldings.Roof.CompatibleContourFiniteSeamClasses
public import Unfoldings.Metric.MappedBankGraftExactness

/-! Actual intrinsic-piece metric classes, including ordinary finite two-bank seams. -/

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

local notation "inside" => K.compatible_section_interior compact nonempty R level higher M

local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance contourGraftExactMeshFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut

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
  (models : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    BankGapModel
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance contourGraftExactWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Pieces" => K.compatibleContourGraftPiece compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour starts W models
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Base" => K.compatibleContourBaseMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Gap" => K.compatibleContourGapMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models

local notation "Index" => K.compatibleContourCellIndex compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Cells" => K.compatibleContourCells compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Inner" => K.compatibleContourCellInner compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Coordinates" => K.compatibleContourCellCoordinates compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "Seams" => K.compatibleContourClosedSeams compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts W models
local notation "Banks" => MetricGluing.bankSeams (MetricGluing.bankStackLeft Pieces Stack Base Gap)
  (MetricGluing.bankStackRight Pieces Stack Base Gap)

/-- The actual whole graft identifies intrinsic piece points exactly along declared bank
chains. This follows from the constructed original closed-cell presentation and finite
classes; no piece-level exactness certificate is assumed. -/
theorem compatibleContourGraft_exact
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event])) :
    MetricGluing.Exact Pieces Banks := by
  apply MetricGluing.exact_of_presentation
    (MetricGluing.NestedCell (fun i j => Cells i j)) Pieces (Seams).relation Banks
    (MetricGluing.mappedNestedPoint Cells Inner Coordinates)
    (MetricGluing.mappedNestedPoint_surjective Cells Inner Coordinates)
    (K.compatibleContourClosedSeamIsometry compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models)
  · rintro ⟨ij, p⟩
    exact K.compatibleContourClosedSeamIsometry_point compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models ij p
  · exact K.compatibleContourClosedSeams_exact compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models geometry
  · intro a b joined
    exact MetricGluing.mappedBankGraftCells_eqvGen_image Cells Inner Coordinates
      (MetricGluing.bankStackLeft Pieces Stack Base Gap)
      (MetricGluing.bankStackRight Pieces Stack Base Gap) a b
      ((K.compatibleContourClosedSeams_relation compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W models a b).mp joined)

/-- Equality in the actual graft is precisely a finite chain of original bank identifications. -/
theorem compatibleContourGraft_point_eq_iff
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (x y : MetricGluing.Total Pieces) :
    MetricGluing.point Pieces Banks x = MetricGluing.point Pieces Banks y ↔
      Relation.EqvGen Banks x y :=
  MetricGluing.point_eq_iff_of_exact Pieces
    (K.compatibleContourGraft_exact compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models geometry) x y

/-- At strict finite-edge times, a graft point has exactly the two consecutive original
intrinsic bank marks as its representatives. This classifies metric equality as well
as the abstract seam relation, including comparisons with all original whole-tail points. -/
theorem compatibleContourFiniteSeam_point_eq_iff
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (vertex : {v : (D).Vertex Set.univ // v ∉ (Fcut).parents.roots})
    (i : Fin ((Stack (.inl vertex)).length + 1))
    (t : unitInterval) (bounds : 0 < t ∧ t < 1) (x : MetricGluing.Total Pieces) :
    MetricGluing.point Pieces Banks
        (MetricGluing.bankStackLeft Pieces Stack Base Gap ⟨.inl vertex, i⟩ t) =
      MetricGluing.point Pieces Banks x ↔
      x = MetricGluing.bankStackLeft Pieces Stack Base Gap ⟨.inl vertex, i⟩ t ∨
        x = MetricGluing.bankStackRight Pieces Stack Base Gap ⟨.inl vertex, i⟩ t :=
  (K.compatibleContourGraft_point_eq_iff compact nonempty R no_boundary level higher M positive
    inner_disk beta acute contour starts W models geometry _ x).trans
    (K.compatibleContourFiniteSeam_eqvGen_iff compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models geometry vertex i t bounds x)

local notation "ParamAt[" b "]" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute b

/-- Any declared bank endpoint in an ordinary finite metric seam class has precisely
the same original seam slot and parameter. This includes all competing terminal endpoints. -/
theorem compatibleContourFiniteSeam_endpoint_parameter_eq
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (vertex : {v : (D).Vertex Set.univ // v ∉ (Fcut).parents.roots})
    (i : Fin ((Stack (.inl vertex)).length + 1)) (t : unitInterval) (bounds : 0 < t ∧ t < 1)
    (other_side : Bool) (other : MetricGluing.BankStackSlot Stack) (s : ParamAt[other.1])
    (equal : MetricGluing.point Pieces Banks
        (MetricGluing.bankStackEndpoint Stack Pieces Base Gap other_side other s) =
      MetricGluing.point Pieces Banks
        (MetricGluing.bankStackLeft Pieces Stack Base Gap ⟨.inl vertex, i⟩ t)) :
    (⟨other, s⟩ : Σ slot : MetricGluing.BankStackSlot Stack, ParamAt[slot.1]) =
      ⟨⟨.inl vertex, i⟩, t⟩ :=
  MetricGluing.bankStackEndpoint_parameter_eq_of_point_eq Stack Pieces Base Gap
    (K.compatibleContourBankStack_nodup compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour)
    (K.compatibleContourGraft_exact compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models geometry) ⟨.inl vertex, i⟩ t
    (K.compatibleContourFiniteMarks_unique compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models geometry vertex t bounds)
    other_side other s equal

end Unfoldings.ConvexRoof
