module

public import Unfoldings.Roof.CompatibleContourSourceOnlyStrictFiber
public import Unfoldings.Roof.CompatibleContourPhysicalVertexAttachments
public import Unfoldings.Roof.CompatibleContourSourceOnlyTerminalJoinClasses

/-! Finite end and tail start name the same arcs at a terminal join. -/

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

local instance sourceOnlyTerminalFiberIndexFintype : Fintype (T).Index :=
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
  (models : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    BankGapModel
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance sourceOnlyTerminalFiberWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Pieces" => polygonalBankStackPiece W.Cut
  (fun event : Event => BankGapModel.region (models event))
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "Gap" => K.compatibleContourSourceOnlyGapMark compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts models

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "BankAt[" e "]" => K.compatibleContourSourceBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "MovedAt[" e "]" => K.compatibleContourSourceOnlyBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "SpatialAt[" e "]" => K.compatibleContourPhysicalBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "Index" => K.compatibleContourSourceOnlyCellIndex compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

local notation "Graft" => K.compatibleContourSourceOnlyGraft compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "FoldAt[" e "]" => K.compatibleContourSourceOnlyFrontierMap compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts models e
local notation "L" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Rgt" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams L Rgt

local notation "Surface" => SpatialEnvelope.wholeSurface M.plane

local notation "Point" => MetricGluing.point Pieces Banks
local notation "Phys" => K.compatibleContourPhysicalAttachmentPoint compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W

local notation "Endpoint" => MetricGluing.bankStackEndpoint Stack Pieces Base Gap
local notation "Terminal" => TriangleComplex.ContourTerminalEdge D Selection

set_option maxHeartbeats 2800000 in
/-- The full fiber at a terminal join is the marked tail stack, including
all incident finite bank end copies. -/
theorem compatibleContourSourceOnlyCollapse_fiber_of_terminal_join
    (geometry : ∀ e : Event, OrientedBankGap BankAt[e] MovedAt[e])
    (f : Graft → Space) (image : Set.range f ⊆ Surface)
    (roof : ∀ x : W.Cut, f (Point ⟨none, x⟩) = (W.partition.restoreCut R.carrier x).val)
    (boundary_gap : ∀ (e : Event) (x : PolygonalPoint (models e).region)
      (h : x.val ∈ frontier (models e).region),
      f (Point ⟨some e, x⟩) = (FoldAt[e] ⟨x.val, h⟩).val)
    (marked : ∀ e : Event, (models e).HasMarkedCollapseFibers (SpatialAt[e])
      (fun y => f (Point ⟨some e, y⟩)))
    (edge : Terminal) (p : Space) (hp : p ∈ Surface)
    (position : Cap.horizontal p = Phys (.inr edge) 0) :
    ContractibleSpace {x : Graft | f x = p} := by
  let bank : Attachment := .inr edge
  let finite : Attachment := .inl ⟨edge.val, edge.property.1⟩
  have locations (a : Attachment) (u : ParamAt a) (same : Phys a u = Phys bank 0) :
      (⟨a, u⟩ : Σ a, ParamAt a) = ⟨bank, 0⟩ ∨
        (⟨a, u⟩ : Σ a, ParamAt a) = ⟨finite, 1⟩ :=
    K.compatibleContourPhysicalAttachmentPoint_at_terminal_join compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W edge a u same
  apply K.compatibleContourSourceOnlyCollapse_fiber_of_address_pairs compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models geometry f image roof
    boundary_gap marked bank 0 ?_ ?_ ?_ ?_ ?_ p hp position
  · intro a u same
    rcases locations a u same with address | address
    · exact congrArg (fun q : Σ a : Attachment, ParamAt a => Stack q.1) address
    · exact (congrArg (fun q : Σ a : Attachment, ParamAt a => Stack q.1) address).trans rfl
  · intro a u same side
    let mark (q : Σ a : Attachment, ParamAt a) := Base q.1 side q.2
    rcases locations a u same with address | address
    · exact congrArg mark address
    · exact (congrArg mark address).trans
        (K.compatibleContourTerminalMark_zero compact nonempty R no_boundary level higher M positive
          inner_disk beta acute contour starts W edge side).symm
  · rintro ⟨a, i⟩ u same
    rcases locations a u same with address | address
    · have eq : a = bank := congrArg Sigma.fst address
      subst a
      have eq : u = 0 := eq_of_heq (Sigma.mk.inj address).2
      subst u
      exact ⟨i, rfl, rfl⟩
    · have eq : a = finite := congrArg Sigma.fst address
      subst a
      have eq : u = 1 := eq_of_heq (Sigma.mk.inj address).2
      subst u
      have endpoint (side : Bool) : Endpoint side ⟨finite, i⟩ 1 = Endpoint side ⟨bank, i⟩ 0 :=
        K.compatibleContourSourceOnlyTerminalJoin_endpoint compact nonempty R no_boundary level
          higher M positive inner_disk beta acute contour starts W models edge i side
      exact ⟨i, endpoint false, endpoint true⟩
  · intro i
    exact K.compatibleContourSourceOnlyTerminalJoin_eqvGen_pair compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W models geometry edge i
  · intro e mem is_source
    change Sum.inr (0 : ℝ≥0) = Sum.inl (0, 0) at is_source
    cases is_source

end Unfoldings.ConvexRoof
