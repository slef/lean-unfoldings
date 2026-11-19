module

public import Unfoldings.Geometry.SourceGapPhysicalCollapse
public import Unfoldings.Roof.CompatibleContourSourceOnlySourceChart
public import Unfoldings.Roof.CompatibleContourPhysicalBanks

/-! Continuous collapse maps on the actual source-only gaps. -/

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

local instance sourceOnlyGapCollapseIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "SourceAt[" q "," i "]" => TriangleComplex.contourOriginalVertex
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) q i
local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
local notation "VertexAt[" q "," e "]" => TriangleComplex.positiveContourVertex D Selection q e

local notation "Event[" q "]" => TriangleComplex.PositiveContourSource D Selection q
local notation "BankAt[" q "," h "," e "]" =>
  K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e
local notation "MovedAt[" q "," h "," e "]" =>
  K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h e

variable
  (contour : (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
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

local notation "Physical[" e "]" => K.compatibleContourPhysicalBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e

/-- Every source-only gap carries a continuous map to its actual original spatial path.
The map preserves the entire finite edge and infinite tail parameters on both banks. -/
theorem compatibleContourSourceOnlyGap_exists_physical_collapse
    (event : Event[contour])
    (G : OrientedBankGap BankAt[contour,starts,event] MovedAt[contour,starts,event]) :
    ∃ f : PolygonalPoint G.model.region → (Physical[event]).carrier, Continuous f ∧
      (∀ (side : Bool)
        (i : Fin (TriangleComplex.positiveContourBankLength D Selection contour event + 1))
        (t : unitInterval), (f (G.model.edgePoint side i t)).val =
          (Physical[event]).addressPoint (.inl (i, t))) ∧
      (∀ (side : Bool) (t : ℝ≥0), (f (G.model.tailPoint side t)).val =
        (Physical[event]).addressPoint (.inr t)) := by
  let first := BankAt[contour,starts,event]
  have genuine (i : Fin (TriangleComplex.positiveContourBankLength D Selection contour event + 1)) :
      first.chain.edge i ≠ 0 := by
    apply norm_ne_zero_iff.mp
    have speed := K.compatibleContourSourceBank_edge_length compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts event i
    exact speed.trans_ne ((D).boundaryBankLength_pos _).ne'
  refine ⟨G.collapseTo Physical[event], G.continuous_collapseTo Physical[event] genuine, ?_, ?_⟩
  · intro side i t
    exact congrArg Subtype.val (G.collapseTo_edgePoint Physical[event] genuine side i t)
  · intro side t
    exact congrArg Subtype.val (G.collapseTo_tailPoint Physical[event] genuine side t)

end Unfoldings.ConvexRoof
