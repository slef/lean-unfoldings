module

public import Unfoldings.Roof.PotentialContourBanks
public import Unfoldings.Complex.ContourSourceBankSides
public import Unfoldings.Complex.ContourProcessedBlocks
public import Unfoldings.Complex.ContourSavedFanAngles
public import Unfoldings.Complex.ContourParentWedgeRun

/-! Angle sums along the saved banks of an arbitrary roof contour. -/

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

/-- Each saved edge retains its original full-cut rootward face and corner tag. -/
theorem contourSourceBankChain_germ (e : Event) (i : Fin (Length[e] + 1)) :
    ((Chain[e]).point i).val =
      (C.contourParentBank Selection contour R.boundary_roots starts
        (R.parents.parent^[i.val] (Source[e]))
        (R.parents.iterate_lt_distanceToRoot_not_mem Source[e]
          (by rw [Span[e]]; exact i.isLt)) false).val := by
  apply C.sourceBank_original_exit Selection contour R.boundary_roots starts
    (C.selectedRetain_subset_processed Selection _) (Chain[e]) Source[e] Span[e]
  · exact R.contourSourceBankChain_original contour starts e
  · exact (R.exists_contourSourceBankChain contour starts e).choose_spec.2.1
  · intro j
    obtain ⟨k, _, raw⟩ := R.contourSourceBankChain_contour contour starts e j
    exact ⟨k, raw⟩

/-- The actual retained fan at an indexed rootward bank point in the source's own stage. -/
def contourSourceBankFanAngle (e : Event)
    (i : Fin (Length[e] + 1)) : ℝ :=
  let retain := RetainAt[e.val.succ]
  C.totalAngle retain (C.boundaryEndVertex retain ((Chain[e]).point i))

/-- Two gap paths through the same incoming child use the same saved fan at its parent.
The index hypotheses identify both rootward banks by their original parent vertex. -/
theorem contourSourceBankFanAngle_eq_of_child
    (child : C.Vertex Set.univ) (nonroot : child ∉ (Parent).roots)
    (a b : Event) (ia : Fin (Length[a] + 1))
    (ib : Fin (Length[b] + 1))
    (inside_a : (Parent).Ancestor Source[a] child)
    (inside_b : (Parent).Ancestor Source[b] child)
    (at_a : (Parent).parent^[ia.val] Source[a] = (Parent).parent child)
    (at_b : (Parent).parent^[ib.val] Source[b] = (Parent).parent child) :
    R.contourSourceBankFanAngle contour starts a ia =
    R.contourSourceBankFanAngle contour starts b ib := by
  let v := (Parent).parent child
  have nonroot_at (e : Event) (i : Fin (Length[e] + 1)) :
      ((Parent).parent^[i.val] Source[e]) ∉ (Parent).roots :=
    (Parent).iterate_lt_distanceToRoot_not_mem Source[e]
      ((Span[e]).symm ▸ i.isLt)
  have v_nonroot : v ∉ (Parent).roots := by
    intro h
    exact (nonroot_at a ia) (Eq.mpr (congrArg (· ∈ (Parent).roots) at_a) h)
  let original (u : C.Vertex Set.univ) (h : u ∉ (Parent).roots) :=
    C.contourParentBank Selection contour R.boundary_roots starts u h false
  have same_end (u : C.Vertex Set.univ) (h : u ∉ (Parent).roots) (hu : u = v) :
      (original u h).val = (original v v_nonroot).val := by
    subst u
    rfl
  have raw (e : Event) (i : Fin (Length[e] + 1))
      (hi : (Parent).parent^[i.val] Source[e] = v) :
      ((Chain[e]).point i).val = (original v v_nonroot).val :=
    (R.contourSourceBankChain_germ contour starts e i).trans
      (same_end _ (nonroot_at e i) hi)
  have original_a :
      C.vertexOfCorner Set.univ (((Chain[a]).point ia).val.1) = v :=
    (R.contourSourceBankChain_original contour starts a ia).trans at_a
  exact C.contour_child_block_totalAngle_eq Selection contour R.boundary_roots starts
    child nonroot a.val b.val inside_a inside_b ((Chain[a]).point ia) ((Chain[b]).point ib)
    ((raw a ia at_a).trans (raw b ib at_b).symm) original_a

private theorem actual_bank_fan_saved_copy
    (e : Event) (i : Fin (Length[e] + 1))
    (v : C.Vertex Set.univ) (nonroot : v ∉ (Parent).roots)
    (same : (Parent).parent^[i.val] Source[e] = v) :
    let stage := RetainAt[e.val.succ]
    let inc := C.selectedRetain_subset_processed Selection FrontierAt[e.val.succ]
    let data := Interval[v,nonroot]
    (Selection).edge ⟨v, nonroot⟩ ∉ stage ∧
      (C.boundaryEndVertex stage ((Chain[e]).point i)) =
        C.vertexForgetCuts inc (C.boundaryEndVertex R.retain (contour.cycle.point data.leave)) := by
  let stage := RetainAt[e.val.succ]
  let data := Interval[v,nonroot]
  have same_named (w : C.Vertex Set.univ) (not_root : w ∉ (Parent).roots)
      (h : w = v) :
      (C.contourParentBank Selection contour R.boundary_roots starts w not_root false).val =
        (contour.cycle.point data.leave).val := by
    subst w
    rfl
  have raw : ((Chain[e]).point i).val = (contour.cycle.point data.leave).val :=
    (R.contourSourceBankChain_germ contour starts e i).trans (same_named _ _ same)
  have boundary : C.IsBoundaryEdge stage (C.germEdge (contour.cycle.point data.leave).val) :=
    (congrArg (C.germEdge) raw) ▸ ((Chain[e]).point i).property
  have side : C.germEdge (contour.cycle.point data.leave).val =
      C.seamSide ((Selection).edge ⟨v, nonroot⟩) (!data.side) :=
    congrArg Subtype.val data.exit_named
  rw [side] at boundary
  have cut : (Selection).edge ⟨v, nonroot⟩ ∉ stage := by
    cases h : !data.side
    · rw [h] at boundary
      exact (C.isBoundaryEdge_left_iff stage _).mp boundary
    · rw [h] at boundary
      exact (C.isBoundaryEdge_right_iff stage _).mp boundary
  exact ⟨cut, congrArg (fun g : C.Germ => C.vertexOfCorner stage g.1) raw⟩

open scoped Classical in
/-- The loss between two literal saved openings at the same parent is the sum of the
actual original roof wedges between the two processing times along the contour. -/
theorem contourSourceBankFanAngle_sub_eq_contour_sum
    (e f : Event) (i : Fin (Length[e] + 1))
    (j : Fin (Length[f] + 1))
    (v : C.Vertex Set.univ) (nonroot : v ∉ (Parent).roots)
    (earlier : e.val.val ≤ f.val.val)
    (old_parent : (Parent).parent^[i.val] Source[e] = v)
    (new_parent : (Parent).parent^[j.val] Source[f] = v) :
    R.contourSourceBankFanAngle contour starts e i -
    R.contourSourceBankFanAngle contour starts f j =
      ∑ t ∈ Finset.univ.filter (fun t : Fin (contour.length + 1) =>
        Visit[t] = v ∧ t ≠ (Interval[v,nonroot]).leave ∧ e.val.val ≤ t.val ∧ t.val < f.val.val),
        C.totalAngle R.retain (C.boundaryEndVertex R.retain (contour.cycle.point t)) := by
  obtain ⟨old_cut, old_fan⟩ := actual_bank_fan_saved_copy R contour starts e i v nonroot old_parent
  obtain ⟨new_cut, new_fan⟩ := actual_bank_fan_saved_copy R contour starts f j v nonroot new_parent
  have formula := C.contourSavedParentFan_angle_sub_eq_sum Selection contour
    R.boundary_roots starts v nonroot e.val.succ f.val.succ (Nat.succ_le_succ earlier)
    old_cut new_cut
  simp only [contourSourceBankFanAngle]
  rw [old_fan, new_fan]
  exact formula

open scoped Classical in
/-- Summing over the ordered roof run gives the same aperture difference as
summing over the corresponding original contour positions. -/
theorem contourSourceBankFanAngle_sub_eq_wedge_run
    (e f : Event) (i : Fin (Length[e] + 1))
    (j : Fin (Length[f] + 1))
    (v : C.Vertex Set.univ) (nonroot : v ∉ (Parent).roots)
    (earlier : e.val.val ≤ f.val.val)
    (old_parent : (Parent).parent^[i.val] Source[e] = v)
    (new_parent : (Parent).parent^[j.val] Source[f] = v)
    (first last : Fin (contour.length + 1))
    (A : C.ContourParentWedgeRun Selection contour R.boundary_roots starts v first last)
    (names : ∀ t : Fin (contour.length + 1), (∃ k, A.visit k = t) ↔
      Visit[t] = v ∧ t ≠ (Interval[v,nonroot]).leave ∧ e.val.val ≤ t.val ∧ t.val < f.val.val) :
    R.contourSourceBankFanAngle contour starts e i -
    R.contourSourceBankFanAngle contour starts f j =
      ∑ k : Fin (A.length + 1), C.totalAngle R.retain
        (C.boundaryEndVertex R.retain (contour.cycle.point (A.visit k))) := by
  classical
  let interval := Finset.univ.filter (fun t : Fin (contour.length + 1) =>
    Visit[t] = v ∧ t ≠ (Interval[v,nonroot]).leave ∧ e.val.val ≤ t.val ∧ t.val < f.val.val)
  let angle (t : Fin (contour.length + 1)) :=
    C.totalAngle R.retain (C.boundaryEndVertex R.retain (contour.cycle.point t))
  have cover : Finset.univ.map A.visit.toEmbedding = interval := by
    ext t
    simp only [interval, Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter]
    exact names t
  rw [R.contourSourceBankFanAngle_sub_eq_contour_sum contour starts e f i j v nonroot earlier
    old_parent new_parent]
  change (∑ t ∈ interval, angle t) = ∑ k, angle (A.visit k)
  rw [← cover, Finset.sum_map]
  rfl

open scoped Classical in
/-- The actual saved gap fan equals the sum of its final named roof wedges. -/
theorem contourSourceBankFanAngle_eq_wedge_run
    (e : Event) (i : Fin (Length[e] + 1))
    (v : C.Vertex Set.univ) (nonroot : v ∉ (Parent).roots)
    (point : (Parent).parent^[i.val] Source[e] = v)
    (first last : Fin (contour.length + 1))
    (A : C.ContourParentWedgeRun Selection contour R.boundary_roots starts v first last)
    (names : ∀ t : Fin (contour.length + 1), (∃ k, A.visit k = t) ↔
      Visit[t] = v ∧ (t = (Interval[v,nonroot]).leave ∨ e.val.val ≤ t.val)) :
    R.contourSourceBankFanAngle contour starts e i =
      ∑ k : Fin (A.length + 1), C.totalAngle R.retain
        (C.boundaryEndVertex R.retain (contour.cycle.point (A.visit k))) := by
  classical
  obtain ⟨cut, saved⟩ := actual_bank_fan_saved_copy R contour starts e i v nonroot point
  let indices := Finset.univ.filter (fun t : Fin (contour.length + 1) =>
    Visit[t] = v ∧ (t = (Interval[v,nonroot]).leave ∨ e.val.val ≤ t.val))
  let angle (t : Fin (contour.length + 1)) :=
    C.totalAngle R.retain (C.boundaryEndVertex R.retain (contour.cycle.point t))
  have cover : Finset.univ.map A.visit.toEmbedding = indices := by
    ext t
    simp only [indices, Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter]
    exact names t
  have formula := C.contourSavedParentFan_angle_eq_sum Selection contour
    R.boundary_roots starts v nonroot e.val.succ cut
  simp only [contourSourceBankFanAngle]
  rw [saved]
  calc
    _ = ∑ t ∈ indices, angle t := by
      simpa only [indices, angle, PotentialCutForest.retain, Fin.val_succ,
        Nat.add_le_add_iff_right] using formula
    _ = ∑ k, angle (A.visit k) := by
      rw [← cover, Finset.sum_map]
      rfl

end Unfoldings.ConvexRoof.PotentialCutForest
