module

public import Unfoldings.Roof.CompatibleContourFiniteMarkUniqueness
public import Unfoldings.Metric.BankStackLocalClasses

/-! Actual ordinary finite seam classes consist of their two consecutive original bank marks. -/

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

local instance contourFiniteSeamMeshFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "ChainAt[" q "," h "," i "," hf "," n "," hn "]" =>
  K.compatibleMeshFreshSourceBankChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h i hf n hn

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
local notation "LengthAt[" q "," e "]" => TriangleComplex.positiveContourBankLength D Selection q e
local notation "SpanAt[" q "," e "]" => TriangleComplex.positiveContourBank_span D Selection q e

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

local instance contourFiniteSeamWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "Parameter" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Pieces" => K.compatibleContourGraftPiece compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour starts W models
local notation "Base" => K.compatibleContourBaseMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Gap" => K.compatibleContourGapMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models

/-- No source is repeated in any actual finite or terminal attachment stack. -/
theorem compatibleContourBankStack_nodup (bank : Attachment) : (Stack bank).Nodup := by
  cases bank with
  | inl vertex => exact (D).contourSavedGapStack_nodup Selection contour vertex.val
  | inr edge => exact (D).contourSavedGapStack_nodup Selection contour edge.val

/-- At a strict finite time, uniqueness of all original marks is derived from the actual
roof and radial gap geometry. No seam-incidence or local chart certificate is supplied. -/
theorem compatibleContourFiniteMarks_unique
    (geometry : ∀ event : (D).PositiveContourSource Selection contour,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (vertex : {v : (D).Vertex Set.univ // v ∉ (Fcut).parents.roots})
    (t : unitInterval) (bounds : 0 < t ∧ t < 1) :
    MetricGluing.BankStackUniqueMarksAt Stack Pieces Base Gap (.inl vertex) t := by
  constructor
  · intro side other other_side s equal
    exact K.compatibleContourBaseMark_eq_finite_interior compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W models vertex other side other_side
      t s bounds equal
  · intro event member side other other_member other_side s equal
    exact K.compatibleContourGapMark_eq_interior compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models event (geometry event) (.inl vertex)
      other member other_member side other_side t s bounds equal

/-- The actual bank-seam class at every strict finite-edge time consists of precisely the
left and right marks of that consecutive seam. Other stack copies stay distinct. -/
theorem compatibleContourFiniteSeam_eqvGen_iff
    (geometry : ∀ event : (D).PositiveContourSource Selection contour,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (vertex : {v : (D).Vertex Set.univ // v ∉ (Fcut).parents.roots})
    (i : Fin ((Stack (.inl vertex)).length + 1))
    (t : unitInterval) (bounds : 0 < t ∧ t < 1) (x : MetricGluing.Total Pieces) :
    Relation.EqvGen
        (MetricGluing.bankSeams (MetricGluing.bankStackLeft Pieces Stack Base Gap)
          (MetricGluing.bankStackRight Pieces Stack Base Gap))
        (MetricGluing.bankStackLeft Pieces Stack Base Gap ⟨.inl vertex, i⟩ t) x ↔
      x = MetricGluing.bankStackLeft Pieces Stack Base Gap ⟨.inl vertex, i⟩ t ∨
        x = MetricGluing.bankStackRight Pieces Stack Base Gap ⟨.inl vertex, i⟩ t :=
  MetricGluing.bankStack_eqvGen_pair_iff Stack Pieces Base Gap
    (K.compatibleContourBankStack_nodup compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour) ⟨.inl vertex, i⟩ t
    (K.compatibleContourFiniteMarks_unique compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models geometry vertex t bounds) x

/-- The two original marks of an ordinary actual finite seam are distinct before grafting.
Their seam relation therefore creates a genuine two-point class of intrinsic piece points. -/
theorem compatibleContourFiniteSeam_endpoints_ne
    (geometry : ∀ event : (D).PositiveContourSource Selection contour,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (vertex : {v : (D).Vertex Set.univ // v ∉ (Fcut).parents.roots})
    (i : Fin ((Stack (.inl vertex)).length + 1)) (t : unitInterval) (bounds : 0 < t ∧ t < 1) :
    MetricGluing.bankStackLeft Pieces Stack Base Gap ⟨.inl vertex, i⟩ t ≠
      MetricGluing.bankStackRight Pieces Stack Base Gap ⟨.inl vertex, i⟩ t := by
  intro equal
  have named := MetricGluing.bankStackEndpoint_eq_of_unique Stack Pieces Base Gap
    (K.compatibleContourBankStack_nodup compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour) ⟨.inl vertex, i⟩ t
    (K.compatibleContourFiniteMarks_unique compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models geometry vertex t bounds)
    true false ⟨.inl vertex, i⟩ t equal
  have impossible := congrArg Prod.fst named
  cases impossible

end Unfoldings.ConvexRoof
