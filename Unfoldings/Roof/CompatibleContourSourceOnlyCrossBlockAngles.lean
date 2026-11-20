module

public import Unfoldings.Roof.CompatibleContourSourceOnlyFanInterval

/-! The two gap bends and the ordered original roof wedges add to a full turn. -/

@[expose] public section

noncomputable section

open scoped NNReal

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

local instance sourceOnlyCrossBlockAnglesIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
local notation "LengthAt[" q "," e "]" => TriangleComplex.positiveContourBankLength D Selection q e
local notation "Event[" q "]" => TriangleComplex.PositiveContourSource D Selection q
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

local notation "Parent" => PotentialCutForest.parents Fcut

local notation "Visit[" j "]" => TriangleComplex.contourOriginalVertex D Selection contour j
local notation "Interval[" v "," h "]" => TriangleComplex.contourParentInterval D Selection contour
  (PotentialCutForest.boundary_roots Fcut) starts v h

local notation "IndexAt[" v "," h "," e "," member "]" =>
  TriangleComplex.contourGapBankIndex D Selection contour v h e
    (Iff.mpr (TriangleComplex.mem_contourEdgeGapStack D Selection contour v e)
      (Iff.mp (TriangleComplex.mem_contourSavedGapStack D Selection contour v e) member))
local notation "AngleAt[" e "," j "]" => K.compatibleContourSourceBankFanAngle compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts e j

/-- Across different child blocks the older moved bank, the intervening roof run,
and the newer original bank have total aperture exactly one full turn. -/
theorem compatibleContourSourceOnlyCrossBlock_angle_balance
    (parent : (D).Vertex Set.univ) (parent_nonroot : parent ∉ (Parent).roots)
    (old new : Event[contour])
    (old_member : old ∈ (D).contourSavedGapStack Selection contour parent)
    (new_member : new ∈ (D).contourSavedGapStack Selection contour parent)
    (earlier : old.val.val ≤ new.val.val)
    (first last : Fin (contour.length + 1))
    (A : (D).ContourParentWedgeRun Selection contour (Fcut).boundary_roots starts parent first last)
    (names : ∀ t : Fin (contour.length + 1), (∃ k, A.visit k = t) ↔ Visit[t] = parent ∧
      t ≠ (Interval[parent,parent_nonroot]).leave ∧ old.val.val ≤ t.val ∧ t.val < new.val.val) :
    let old_angle := AngleAt[old,IndexAt[parent,parent_nonroot,old,old_member]]
    let new_angle := AngleAt[new,IndexAt[parent,parent_nonroot,new,new_member]]
    (2 * Real.pi - old_angle) +
        (∑ k : Fin (A.length + 1), (D).totalAngle (Fcut).retain
          ((D).boundaryEndVertex (Fcut).retain (contour.cycle.point (A.visit k)))) + new_angle =
      2 * Real.pi := by
  let i := IndexAt[parent,parent_nonroot,old,old_member]
  let j := IndexAt[parent,parent_nonroot,new,new_member]
  have formula := K.compatibleContourSourceBankFanAngle_sub_eq_wedge_run compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts old new i j parent
    parent_nonroot earlier
    ((D).contourGapBankIndex_original Selection contour parent parent_nonroot old _)
    ((D).contourGapBankIndex_original Selection contour parent parent_nonroot new _)
    first last A names
  change (2 * Real.pi - AngleAt[old,i]) + _ + AngleAt[new,j] = 2 * Real.pi
  rw [← formula]
  ring

end Unfoldings.ConvexRoof
