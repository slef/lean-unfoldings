module

public import Unfoldings.Complex.ContourBetweenChildBlocks
public import Unfoldings.Roof.CompatibleContourRoofVertexMarks

/-! The two actual original bank addresses at a wedge between child excursions. -/

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

local instance sourceOnlyRoofWedgeMarksFintype : Fintype (T).Index :=
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

local instance sourceOnlyRoofWedgeWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "Retain" => PotentialCutForest.retain Fcut
local notation "VertexAt[" w "]" => TriangleComplex.vertexPoint D Retain w
local notation "Forget[" w "]" => TriangleComplex.vertexForgetCuts D (Set.subset_univ Retain) w
local notation "Height[" x "]" => SlopeEnvelope.height (K.clippedExtension slopes compact nonempty)
  (Cap.horizontal (SpatialFolding.toSpace
    (SpatialEnvelope.Triangulation.pairedFolding
      (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) Retain x))
local notation "BankAt[" e "," side "]" => TriangleComplex.contourParentBank D Selection contour
  (PotentialCutForest.boundary_roots Fcut) starts (Subtype.val e) (Subtype.property e) side

local notation "Edge" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute

/-- Every finite roof copy of an original nonroot lies strictly below the
completion level. -/
theorem compatibleContourRoofVertex_height_lt_of_nonroot
    (w : (D).Vertex Retain) (nonroot : Forget[w] ∉ (Fcut).parents.roots) :
    Height[VertexAt[w]] < level := by
  have position : (T).pairedFolding.toSpace Retain VertexAt[w] =
      (T).pairedFolding.toSpace Set.univ ((D).vertexPoint Set.univ Forget[w]) := by
    rw [(D).vertexPoint_vertexForgetCuts, (T).pairedFolding.toSpace_forgetCuts]
  exact (congrArg (fun p : Space => (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal p)) position).trans_lt
      (K.compatibleMesh_nonroot_height_lt compact nonempty R no_boundary level higher M positive
        inner_disk beta acute Forget[w] nonroot)

/-- A particular final roof wedge records both incident child bank copies, and no other
original attachment marks meet its center. -/
theorem compatibleContourSourceOnlyRoofWedge_baseMark_iff
    (old_child new_child : Edge) (j : Fin (contour.length + 1))
    (after_old : finRotate (contour.length + 1) ((D).contourParentInterval Selection contour
      (Fcut).boundary_roots starts old_child.val old_child.property).leave = j)
    (before_new : ((D).contourParentInterval Selection contour (Fcut).boundary_roots starts
      new_child.val new_child.property).enter = j)
    (nonroot : (D).contourOriginalVertex Selection contour j ∉ (Fcut).parents.roots)
    (bank : Attachment) (side : Bool) (t : ParamAt bank) :
    let w := (D).boundaryEndVertex Retain (contour.cycle.point j)
    Base bank side t = Map VertexAt[w] ↔
      (⟨bank, t⟩ : Σ b : Attachment, ParamAt b) = ⟨.inl old_child, 1⟩ ∧ side = false ∨
      (⟨bank, t⟩ : Σ b : Attachment, ParamAt b) = ⟨.inl new_child, 1⟩ ∧ side = true := by
  let w := (D).boundaryEndVertex Retain (contour.cycle.point j)
  have below := K.compatibleContourRoofVertex_height_lt_of_nonroot compact nonempty R no_boundary
    level higher M positive inner_disk beta acute w nonroot
  have germs := (D).contour_parent_wedge_end_eq_iff Selection contour (Fcut).boundary_roots
    starts old_child new_child j after_old before_new
  have tags : Function.Injective (fun p : Edge × Bool =>
      BankAt[p.1,p.2]) :=
    (D).contourParentBank_injective Selection contour (Fcut).boundary_roots starts
  have no_reverse (a b : Edge) (x y : Bool) :
      BankAt[a,x] ≠ (D).boundaryTurn Retain BankAt[b,y] := by
    intro h
    have equal := ((D).boundaryEnd_bank_eq_iff Retain _ _).mpr (Or.inr h)
    have same : (a, x) = (b, y) :=
      (D).contourParentBank_bank_injective Selection contour (Fcut).boundary_roots starts equal
    cases same
    exact (D).boundaryTurn_ne Retain BankAt[a,x] h.symm
  constructor
  · intro mark
    cases bank with
    | inr tail => exact (K.compatibleContourRoofVertex_ne_tailMark compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts W w below tail side t mark).elim
    | inl e =>
      have ends := (K.compatibleContourRoofVertex_eq_parentMark_iff compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts W w below e side t).mp mark
      rcases ends with ⟨rfl, start⟩ | ⟨rfl, finish⟩
      · rcases (germs _).mp start.symm with old | new
        · exact (no_reverse _ _ _ _ old).elim
        · exact (no_reverse _ _ _ _ new).elim
      · rcases (germs _).mp finish.symm with old | new
        · have same : (e, side) = (old_child, false) :=
            tags (((D).boundaryTurn_involutive Retain).injective old)
          cases same
          exact Or.inl ⟨rfl, rfl⟩
        · have same : (e, side) = (new_child, true) :=
            tags (((D).boundaryTurn_involutive Retain).injective new)
          cases same
          exact Or.inr ⟨rfl, rfl⟩
  · rintro (⟨same, rfl⟩ | ⟨same, rfl⟩)
    · cases same
      exact (K.compatibleContourRoofVertex_eq_parentMark_iff compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts W w below old_child false 1).mpr
        (Or.inr ⟨rfl, ((germs _).mpr (Or.inl rfl)).symm⟩)
    · cases same
      exact (K.compatibleContourRoofVertex_eq_parentMark_iff compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts W w below new_child true 1).mpr
        (Or.inr ⟨rfl, ((germs _).mpr (Or.inr rfl)).symm⟩)

end Unfoldings.ConvexRoof
