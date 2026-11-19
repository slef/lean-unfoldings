module

public import Unfoldings.Roof.CompatibleContourTerminalSeamClasses
public import Unfoldings.Geometry.BankGapJoinAddresses

/-! Original finite and terminal addresses of a literal join are determined. -/

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

local instance contourTerminalJoinMarkMeshFintype : Fintype (T).Index :=
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

local instance contourTerminalJoinMarkWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Pieces" => K.compatibleContourGraftPiece compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour starts W models
local notation "Base" => K.compatibleContourBaseMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Gap" => K.compatibleContourGapMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models

local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute

local notation "Edge" => TriangleComplex.ContourTerminalEdge D Selection


local notation "Child[" e "]" => (Subtype.mk (Subtype.val e) (And.left (Subtype.property e)))
local notation "LastPair[" e "]" => (Sigma.mk (Sum.inl Child[e]) 1 : Σ b : Attachment, ParamAt b)
local notation "TailPair[" e "]" => (Sigma.mk (Sum.inr e) 0 : Σ b : Attachment, ParamAt b)

/-- At the actual join, roof marks recover the precise original side and the two
allowed original addresses, including the coincident finite endpoint. -/
theorem compatibleContourBaseMark_eq_terminal_join
    (edge : Edge) (other : Attachment) (side other_side : Bool) (s : ParamAt other)
    (equal : Base other other_side s = Base (.inr edge) side 0) :
    other_side = side ∧
      ((⟨other, s⟩ : Σ b, ParamAt b) = TailPair[edge] ∨
        (⟨other, s⟩ : Σ b, ParamAt b) = LastPair[edge]) := by
  have label (e : Edge) (t : ℝ≥0)
      (eq : Base (.inr e) other_side t = Base (.inr edge) side 0) :
      (e, other_side, t) = (edge, side, 0) :=
    K.compatibleContourTerminalMark_eq compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W edge e side other_side 0 t eq
  cases other with
  | inr e =>
    have named := label e s equal
    have e_eq := congrArg Prod.fst named
    have flag := congrArg (fun p => p.2.1) named
    have time := congrArg (fun p => p.2.2) named
    dsimp only at e_eq flag time
    subst e
    subst s
    exact ⟨flag, Or.inl rfl⟩
  | inl vertex =>
    have lower := K.compatibleContourTerminalMark_height_ge compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W edge side 0
    let height (x : W.Cut) := (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut R.carrier x).val)
    have height_bound : level ≤ height (Base (.inl vertex) other_side s) :=
      lower.trans_eq (congrArg height equal.symm)
    have time : s = 1 := by
      apply Subtype.ext
      by_contra hn
      have before : s < 1 := lt_of_le_of_ne s.property.2 (fun eq => hn (congrArg Subtype.val eq))
      exact (not_lt_of_ge height_bound) (K.compatibleContourParentMark_height_lt compact
        nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W
        vertex.val vertex.property other_side s before)
    subst s
    let parent := (Fcut).parents.parent vertex.val
    have parent_root : parent ∈ (Fcut).parents.roots := by
      by_contra nonroot
      have below := K.compatibleMesh_nonroot_height_lt compact nonempty R no_boundary level higher
        M positive inner_disk beta acute parent nonroot
      let bank := (D).contourParentBank Selection contour (Fcut).boundary_roots starts vertex.val
        vertex.property other_side
      have restore := K.restore_compatibleMeshWholeMap compact nonempty R no_boundary level higher
        M positive inner_disk beta acute W ((D).directedBoundaryPath bank 1)
      have position := (T).pairedFolding.contourParentBank_position Selection contour
        (Fcut).boundary_roots starts vertex.val vertex.property other_side 1
      have at_end : (T).pairedFolding.toSpace (Fcut).retain
          ((D).directedBoundaryPath bank 1) =
            (T).pairedFolding.toSpace Set.univ ((D).vertexPoint Set.univ parent) :=
        position.trans (AffineMap.lineMap_apply_one _ _)
      have height_eq : height (Base (.inl vertex) other_side 1) =
          (K.clippedExtension slopes compact nonempty).height
            (Cap.horizontal ((T).pairedFolding.toSpace Set.univ
              ((D).vertexPoint Set.univ parent))) :=
        congrArg (fun x => (K.clippedExtension slopes compact nonempty).height (Cap.horizontal x))
          (restore.trans at_end)
      exact (not_lt_of_ge (height_bound.trans_eq height_eq)) below
    let e : Edge := ⟨vertex.val, vertex.property, parent_root⟩
    have eq : Base (.inr e) other_side 0 = Base (.inr edge) side 0 :=
      (K.compatibleContourTerminalMark_zero compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W e other_side).trans equal
    have named := label e 0 eq
    have flag : other_side = side := congrArg (fun p => p.2.1) named
    have vertex_eq : vertex = Child[edge] := Subtype.ext
      (congrArg (fun p => p.1.val) named)
    subst vertex
    exact ⟨flag, Or.inr rfl⟩

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "AddressAt[" b "," e "," h "," t "]" => K.compatibleContourGapAddress compact
  nonempty R no_boundary level higher M positive inner_disk beta acute contour b e h t

/-- The literal gap join retains its side and only its original two adjacent addresses. -/
theorem compatibleContourGapMark_eq_terminal_join
    (event : Event) (geometry : OrientedBankGap (BankAt[contour,starts,event])
      (OpenedAt[contour,starts,event]))
    (edge : Edge) (other : Attachment) (member : event ∈ Stack (.inr edge))
    (other_member : event ∈ Stack other) (side other_side : Bool) (s : ParamAt other)
    (equal : Gap other event other_member other_side s = Gap (.inr edge) event member side 0) :
    other_side = side ∧
      ((⟨other, s⟩ : Σ b, ParamAt b) = TailPair[edge] ∨
        (⟨other, s⟩ : Σ b, ParamAt b) = LastPair[edge]) := by
  have position : (models event).addressFrontier other_side AddressAt[other,event,other_member,s] =
      (models event).addressFrontier side (.inr 0) := by
    apply Subtype.ext
    exact (K.compatibleContourGapMark_address compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models other event other_member other_side
      s).symm.trans (congrArg PolygonalPoint.val equal)
  have named := (models event).addressFrontier_eq_tail_zero geometry
    (K.compatibleContourGapBank_edge_ne_zero compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts models event) side other_side _ position
  refine ⟨named.1, ?_⟩
  rcases named.2 with tail | last
  · exact Or.inl (K.compatibleContourGapAddress_eq compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour event (.inr edge) other member other_member 0 s tail)
  · let child : {v : (D).Vertex Set.univ // v ∉ (Fcut).parents.roots} := Child[edge]
    have last_member : event ∈ Stack (.inl child) := member
    have index : AddressAt[.inl child,event,last_member,1] =
        .inl (Fin.last ((D).positiveContourBankLength Selection contour event), 1) := by
      unfold compatibleContourGapAddress
      have at_edge := ((D).mem_contourEdgeGapStack Selection contour edge.val event).mpr
        (((D).mem_contourSavedGapStack Selection contour edge.val event).mp member)
      exact congrArg (fun i => Sum.inl (i, (1 : unitInterval)))
        ((D).contourGapBankIndex_last Selection contour edge event at_edge)
    exact Or.inr (K.compatibleContourGapAddress_eq compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour event (.inl child) other last_member other_member 1 s
      (last.trans index.symm))

end Unfoldings.ConvexRoof
