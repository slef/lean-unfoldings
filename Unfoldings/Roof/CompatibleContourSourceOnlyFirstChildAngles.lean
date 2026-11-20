module

public import Unfoldings.Roof.CompatibleContourSourceOnlyFanInterval
public import Unfoldings.Complex.ContourParentWedgePartition

/-! The original leading roof wedges and the saved first-child fan fill the parent angle. -/

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

local instance sourceOnlyFirstChildAnglesIndexFintype : Fintype (T).Index :=
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



/-- The roof run before the first child, its saved bend angle, and the original
parent defect add to one full turn. -/
theorem compatibleContourSourceOnlyFirstChild_angle_balance
    (parent child : (D).Vertex Set.univ)
    (parent_nonroot : parent ∉ (Parent).roots) (child_nonroot : child ∉ (Parent).roots)
    (at_parent : (Parent).parent child = parent)
    (e : Event[contour])
    (in_child : (Parent).Ancestor ((D).positiveContourVertex Selection contour e) child)
    (member : e ∈ (D).contourSavedGapStack Selection contour parent)
    (A : (D).ContourParentWedgeRun Selection contour (Fcut).boundary_roots starts parent
      (finRotate (contour.length + 1) (Interval[parent,parent_nonroot]).enter)
      (Interval[child,child_nonroot]).enter) :
    let saved := AngleAt[e,IndexAt[parent,parent_nonroot,e,member]]
    saved + (∑ k : Fin (A.length + 1), (D).totalAngle (Fcut).retain
      ((D).boundaryEndVertex (Fcut).retain (contour.cycle.point (A.visit k)))) +
      (D).interiorAngularDefect Set.univ parent = 2 * Real.pi := by
  let p := Interval[parent,parent_nonroot]
  let c := Interval[child,child_nonroot]
  let first := finRotate (contour.length + 1) c.leave
  have at_first : Visit[first] = parent :=
    ((D).contourChild_consecutive_parent_visits Selection contour (Fcut).boundary_roots starts
      child child_nonroot (at_parent.symm ▸ parent_nonroot)).2.2.1.trans at_parent
  have at_last : Visit[p.leave] = parent :=
    ((D).contourParentInterval_exit_original Selection contour (Fcut).boundary_roots starts
      parent parent_nonroot).1
  have ordered : first ≤ p.leave := ((p.subtree first).mp
    (at_first.symm ▸ (Parent).ancestor_refl parent)).2
  let B := (D).contourParentWedgeRun Selection contour (Fcut).boundary_roots starts parent
    parent_nonroot first p.leave ordered at_first at_last
  let i := IndexAt[parent,parent_nonroot,e,member]
  have names (j : Fin (contour.length + 1)) : (∃ k, B.visit k = j) ↔
      Visit[j] = parent ∧ (j = p.leave ∨ e.val.val ≤ j.val) := by
    rw [B.visits j]
    constructor
    · rintro ⟨here, after, before⟩
      exact ⟨here, ((D).contour_parent_visit_in_saved_suffix_iff Selection contour
        (Fcut).boundary_roots starts ⟨parent, parent_nonroot⟩ ⟨child, child_nonroot⟩
        at_parent e in_child j here).mpr ⟨after, before⟩⟩
    · rintro ⟨here, suffix⟩
      exact ⟨here, ((D).contour_parent_visit_in_saved_suffix_iff Selection contour
        (Fcut).boundary_roots starts ⟨parent, parent_nonroot⟩ ⟨child, child_nonroot⟩
        at_parent e in_child j here).mp suffix⟩
  have sum := K.compatibleContourSourceBankFanAngle_eq_wedge_run compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts e i parent parent_nonroot
    ((D).contourGapBankIndex_original Selection contour parent parent_nonroot e _) _ _ B names
  have complete := (D).contourParentWedgeRun_sum_prefix_add_suffix Selection contour
    (Fcut).boundary_roots starts ⟨parent, parent_nonroot⟩ ⟨child, child_nonroot⟩ at_parent A B
  have interior : ¬ (D).IsBoundaryVertex Set.univ parent :=
    fun boundary => parent_nonroot ((Fcut).boundary_roots boundary)
  let angle (j : Fin (contour.length + 1)) := (D).totalAngle (Fcut).retain
    ((D).boundaryEndVertex (Fcut).retain (contour.cycle.point j))
  change (∑ k, angle (A.visit k)) + (∑ k, angle (B.visit k)) =
    (D).totalAngle Set.univ parent at complete
  change AngleAt[e,i] + (∑ k, angle (A.visit k)) +
    (D).interiorAngularDefect Set.univ parent = _
  have saved : AngleAt[e,i] = ∑ k, angle (B.visit k) := sum
  rw [TriangleComplex.interiorAngularDefect, ite_eq_right interior, saved,
    add_comm (∑ k, angle (B.visit k)), complete]
  ring

end Unfoldings.ConvexRoof
