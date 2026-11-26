module

public import Unfoldings.Roof.PotentialContourFanAngles
public import Unfoldings.Complex.ContourParentWedgePartition
public import Unfoldings.Complex.ContourExtremeChildWedgeRun
public import Unfoldings.Roof.CurvatureNonnegative
public import Unfoldings.Complex.ContourSourceCoverage


/-! The aperture balance between original roof wedges and saved source gaps. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.PotentialCutForest

open Real
open scoped NNReal ENNReal

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {f : Plane → ℝ} {cuts : Set Plane} (R : K.PotentialCutForest f cuts)
  (contour : C.BoundaryContour R.retain)
  (starts : C.contourOriginalVertex R.selection contour 0 ∈ R.parents.roots)


local notation "Selection" => PotentialCutForest.selection R
local notation "Parent" => PotentialCutForest.parents R
local notation "Event" => TriangleComplex.PositiveContourSource C Selection contour
local notation "Length[" e "]" => TriangleComplex.positiveContourBankLength C Selection contour e
local notation "Source[" e "]" => TriangleComplex.positiveContourVertex C Selection contour e
local notation "Span[" e "]" => TriangleComplex.positiveContourBank_span C Selection contour e
local notation "FrontierAt[" i "]" => TriangleComplex.contourFrontier C Selection contour i
local notation "RetainAt[" i "]" => TriangleComplex.processedParentRetain C Selection FrontierAt[i]
local notation "Chain[" e "]" => PotentialCutForest.contourSourceBankChain R contour starts e
local notation "Visit[" j "]" => TriangleComplex.contourOriginalVertex C Selection contour j
local notation "Interval[" v "," h "]" => TriangleComplex.contourParentInterval
  C Selection contour (PotentialCutForest.boundary_roots R) starts v h

local notation "IndexAt[" v "," h "," e "," member "]" =>
  TriangleComplex.contourGapBankIndex C Selection contour v h e
    (Iff.mpr (TriangleComplex.mem_contourEdgeGapStack C Selection contour v e)
      (Iff.mp (TriangleComplex.mem_contourSavedGapStack C Selection contour v e) member))
local notation "AngleAt[" e "," j "]" => PotentialCutForest.contourSourceBankFanAngle
  R contour starts e j

/-- The roof run before the first child, its saved bend angle, and the original
parent defect add to one full turn. -/
theorem contourGraftFirstChild_angle_balance
    (parent child : C.Vertex Set.univ)
    (parent_nonroot : parent ∉ (Parent).roots) (child_nonroot : child ∉ (Parent).roots)
    (at_parent : (Parent).parent child = parent)
    (e : Event)
    (in_child : (Parent).Ancestor (C.positiveContourVertex Selection contour e) child)
    (member : e ∈ C.contourSavedGapStack Selection contour parent)
    (A : C.ContourParentWedgeRun Selection contour R.boundary_roots starts parent
      (finRotate (contour.length + 1) (Interval[parent,parent_nonroot]).enter)
      (Interval[child,child_nonroot]).enter) :
    let saved := AngleAt[e,IndexAt[parent,parent_nonroot,e,member]]
    saved + (∑ k : Fin (A.length + 1), C.totalAngle R.retain
      (C.boundaryEndVertex R.retain (contour.cycle.point (A.visit k)))) +
      C.interiorAngularDefect Set.univ parent = 2 * Real.pi := by
  let p := Interval[parent,parent_nonroot]
  let c := Interval[child,child_nonroot]
  let first := finRotate (contour.length + 1) c.leave
  have at_first : Visit[first] = parent :=
    (C.contourChild_consecutive_parent_visits Selection contour R.boundary_roots starts
      child child_nonroot (at_parent.symm ▸ parent_nonroot)).2.2.1.trans at_parent
  have at_last : Visit[p.leave] = parent :=
    (C.contourParentInterval_exit_original Selection contour R.boundary_roots starts
      parent parent_nonroot).1
  have ordered : first ≤ p.leave := ((p.subtree first).mp
    (at_first.symm ▸ (Parent).ancestor_refl parent)).2
  let B := C.contourParentWedgeRun Selection contour R.boundary_roots starts parent
    parent_nonroot first p.leave ordered at_first at_last
  let i := IndexAt[parent,parent_nonroot,e,member]
  have names (j : Fin (contour.length + 1)) : (∃ k, B.visit k = j) ↔
      Visit[j] = parent ∧ (j = p.leave ∨ e.val.val ≤ j.val) := by
    rw [B.visits j]
    constructor
    · rintro ⟨here, after, before⟩
      exact ⟨here, (C.contour_parent_visit_in_saved_suffix_iff Selection contour
        R.boundary_roots starts ⟨parent, parent_nonroot⟩ ⟨child, child_nonroot⟩
        at_parent e in_child j here).mpr ⟨after, before⟩⟩
    · rintro ⟨here, suffix⟩
      exact ⟨here, (C.contour_parent_visit_in_saved_suffix_iff Selection contour
        R.boundary_roots starts ⟨parent, parent_nonroot⟩ ⟨child, child_nonroot⟩
        at_parent e in_child j here).mp suffix⟩
  have sum := R.contourSourceBankFanAngle_eq_wedge_run contour starts e i parent parent_nonroot
    (C.contourGapBankIndex_original Selection contour parent parent_nonroot e _) _ _ B names
  have complete := C.contourParentWedgeRun_sum_prefix_add_suffix Selection contour
    R.boundary_roots starts ⟨parent, parent_nonroot⟩ ⟨child, child_nonroot⟩ at_parent A B
  have interior : ¬ C.IsBoundaryVertex Set.univ parent :=
    fun boundary => parent_nonroot (R.boundary_roots boundary)
  let angle (j : Fin (contour.length + 1)) := C.totalAngle R.retain
    (C.boundaryEndVertex R.retain (contour.cycle.point j))
  change (∑ k, angle (A.visit k)) + (∑ k, angle (B.visit k)) =
    C.totalAngle Set.univ parent at complete
  change AngleAt[e,i] + (∑ k, angle (A.visit k)) +
    C.interiorAngularDefect Set.univ parent = _
  have saved : AngleAt[e,i] = ∑ k, angle (B.visit k) := sum
  rw [TriangleComplex.interiorAngularDefect, ite_eq_right interior, saved,
    add_comm (∑ k, angle (B.visit k)), complete]
  ring

/-- The final roof run complements the last gap bend to exactly one turn. -/
theorem contourGraftLastChild_angle_balance
    (parent child : C.Vertex Set.univ)
    (parent_nonroot : parent ∉ (Parent).roots) (child_nonroot : child ∉ (Parent).roots)
    (at_parent : (Parent).parent child = parent)
    (e : Event)
    (in_child : (Parent).Ancestor (C.positiveContourVertex Selection contour e) child)
    (member : e ∈ C.contourSavedGapStack Selection contour parent)
    (A : C.ContourParentWedgeRun Selection contour R.boundary_roots starts parent
      (finRotate (contour.length + 1) (Interval[child,child_nonroot]).leave)
      (Interval[parent,parent_nonroot]).leave) :
    let saved := AngleAt[e,IndexAt[parent,parent_nonroot,e,member]]
    (2 * Real.pi - saved) + (∑ k : Fin (A.length + 1), C.totalAngle R.retain
      (C.boundaryEndVertex R.retain (contour.cycle.point (A.visit k)))) = 2 * Real.pi := by
  let i := IndexAt[parent,parent_nonroot,e,member]
  have names (j : Fin (contour.length + 1)) : (∃ k, A.visit k = j) ↔
      Visit[j] = parent ∧ (j = (Interval[parent,parent_nonroot]).leave ∨ e.val.val ≤ j.val) := by
    rw [A.visits j]
    constructor
    · rintro ⟨here, first, last⟩
      exact ⟨here, (C.contour_parent_visit_in_saved_suffix_iff Selection contour
        R.boundary_roots starts ⟨parent, parent_nonroot⟩ ⟨child, child_nonroot⟩
        at_parent e in_child j here).mpr ⟨first, last⟩⟩
    · rintro ⟨here, suffix⟩
      exact ⟨here, (C.contour_parent_visit_in_saved_suffix_iff Selection contour
        R.boundary_roots starts ⟨parent, parent_nonroot⟩ ⟨child, child_nonroot⟩
        at_parent e in_child j here).mp suffix⟩
  have sum := R.contourSourceBankFanAngle_eq_wedge_run contour starts e i parent parent_nonroot
    (C.contourGapBankIndex_original Selection contour parent parent_nonroot e _) _ _ A names
  change (2 * Real.pi - AngleAt[e,i]) + _ = _
  rw [← sum]
  ring

/-- Across different child blocks the older moved bank, the intervening roof run,
and the newer original bank have total aperture exactly one full turn. -/
theorem contourGraftCrossBlock_angle_balance
    (parent : C.Vertex Set.univ) (parent_nonroot : parent ∉ (Parent).roots)
    (old new : Event)
    (old_member : old ∈ C.contourSavedGapStack Selection contour parent)
    (new_member : new ∈ C.contourSavedGapStack Selection contour parent)
    (earlier : old.val.val ≤ new.val.val)
    (first last : Fin (contour.length + 1))
    (A : C.ContourParentWedgeRun Selection contour R.boundary_roots starts parent first last)
    (names : ∀ t : Fin (contour.length + 1), (∃ k, A.visit k = t) ↔ Visit[t] = parent ∧
      t ≠ (Interval[parent,parent_nonroot]).leave ∧ old.val.val ≤ t.val ∧ t.val < new.val.val) :
    let old_angle := AngleAt[old,IndexAt[parent,parent_nonroot,old,old_member]]
    let new_angle := AngleAt[new,IndexAt[parent,parent_nonroot,new,new_member]]
    (2 * Real.pi - old_angle) +
        (∑ k : Fin (A.length + 1), C.totalAngle R.retain
          (C.boundaryEndVertex R.retain (contour.cycle.point (A.visit k)))) + new_angle =
      2 * Real.pi := by
  let i := IndexAt[parent,parent_nonroot,old,old_member]
  let j := IndexAt[parent,parent_nonroot,new,new_member]
  have formula := R.contourSourceBankFanAngle_sub_eq_wedge_run contour starts old new i j parent
    parent_nonroot earlier
    (C.contourGapBankIndex_original Selection contour parent parent_nonroot old _)
    (C.contourGapBankIndex_original Selection contour parent parent_nonroot new _)
    first last A names
  change (2 * Real.pi - AngleAt[old,i]) + _ + AngleAt[new,j] = 2 * Real.pi
  rw [← formula]
  ring

include starts in
/-- Without its own source event, an interior cut vertex carries no angular defect. -/
theorem contourGraft_defect_eq_zero_of_no_last_source
    (ends : Visit[Fin.last contour.length] ∈ (Parent).roots)
    (v : C.Vertex Set.univ) (nonroot : v ∉ (Parent).roots)
    (absent : ∀ e : Event, (C.contourSavedGapStack Selection contour v).getLast? = some e →
      Source[e] ≠ v) :
    C.interiorAngularDefect Set.univ v = 0 := by
  apply le_antisymm _ (K.interiorCurvature_nonneg v)
  by_contra! positive
  obtain ⟨e, eq⟩ := C.exists_positiveContourSource_of_defect Selection contour
    R.boundary_roots starts ends v nonroot positive
  obtain ⟨earlier, stack⟩ := C.contourSavedGapStack_source_last Selection contour
    R.boundary_roots starts e
  have shape : C.contourSavedGapStack Selection contour v = earlier ++ [e] := eq ▸ stack
  have last : (C.contourSavedGapStack Selection contour v).getLast? = some e := by
    rw [shape, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil e []), List.getLast?_singleton]
  exact absent e last eq

end Unfoldings.ConvexRoof.PotentialCutForest
