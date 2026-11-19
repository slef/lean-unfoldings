module

public import Unfoldings.Roof.CompatibleContourGapMarkUniqueness
public import Unfoldings.Roof.CompatibleContourRoofMarkSeparation

/-! Actual roof and gap mark uniqueness at each strict finite forest-edge attachment. -/

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

local instance contourFiniteMarkMeshFintype : Fintype (T).Index :=
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

local instance contourFiniteMarkWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "Parameter" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "BaseAt[" b "," side "," t "]" => K.compatibleContourBaseMark compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts W models b side t

/-- At a finite-edge interior, a roof mark retains its attachment, side, and parameter
among all actual finite and whole-tail roof marks. -/
theorem compatibleContourBaseMark_eq_finite_interior
    (vertex : {v : (D).Vertex Set.univ // v ∉ (Fcut).parents.roots})
    (other : Attachment) (side other_side : Bool) (t : unitInterval) (s : Parameter other)
    (bounds : 0 < t ∧ t < 1)
    (equal : BaseAt[other,other_side,s] = BaseAt[.inl vertex,side,t]) :
    other_side = side ∧ (⟨other, s⟩ : Σ b, Parameter b) = ⟨.inl vertex, t⟩ := by
  cases other with
  | inl other =>
    have named := K.compatibleContourParentMark_eq_interior compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W vertex other side other_side t s
      bounds equal
    have vertices := congrArg (fun p => p.1) named
    have flags := congrArg (fun p => p.2.1) named
    have times := congrArg (fun p => p.2.2) named
    dsimp only at vertices flags times
    subst other
    subst s
    exact ⟨flags, rfl⟩
  | inr edge =>
    exact (K.compatibleContourTerminalMark_ne_parent_interior compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W edge other_side s vertex.val
      vertex.property side t bounds.2 equal).elim

end Unfoldings.ConvexRoof
