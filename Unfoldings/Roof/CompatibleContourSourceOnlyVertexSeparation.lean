module

public import Unfoldings.Metric.BankStackSlotCases
public import Unfoldings.Metric.BankStackClassTimes
public import Unfoldings.Roof.CompatibleContourSourceOnlyChildPairClasses
public import Unfoldings.Roof.CompatibleContourSourceOnlyCrossBlockClasses
public import Unfoldings.Roof.CompatibleContourSourceOnlyFirstChildClass
public import Unfoldings.Roof.CompatibleContourSourceOnlyLastChildClass
public import Unfoldings.Roof.CompatibleContourSourceOnlyTipAndChildClass
public import Unfoldings.Roof.CompatibleContourSourceOnlyLabels

/-! Separation of outgoing stack slots at an original nonroot vertex. -/

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

local instance sourceOnlyVertexSeparationIndexFintype : Fintype (T).Index :=
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
  (geometry : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    OrientedBankGap
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance sourceOnlyVertexSeparationWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "models" => (fun event : Event => OrientedBankGap.model (geometry event))
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
local notation "FiniteBank[" v "," h "]" => (Sum.inl (Subtype.mk v h) : Attachment)
local notation "Named" => MetricGluing.bankStackEndpointAddress (Parameter := ParamAt) Stack
local notation "EndAt" => MetricGluing.bankStackEndpoint Stack Pieces Base Gap
local notation "L" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Rgt" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams L Rgt
local notation "Time" => (Σ s : MetricGluing.BankStackSlot Stack, ParamAt (Sigma.fst s))

local notation "Edge" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "SourceOf[" e "]" => TriangleComplex.positiveContourVertex D Selection contour e

local notation "Point" => MetricGluing.point Pieces Banks

omit beta acute in
private theorem eq_nil_of_last_named {G : Type*} (before after : List G) (g : G)
    (nodup : (before ++ g :: after).Nodup)
    (last : (before ++ g :: after).getLast? = some g) : after = [] := by
  by_contra hn
  rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
    List.getLast?_cons_of_ne_nil hn] at last
  exact (List.nodup_cons.mp (List.nodup_append'.mp nodup).2.1).1
    (List.mem_of_mem_getLast? (last.symm ▸ (show g ∈ (some g : Option G) by simp)))

set_option maxHeartbeats 5300000 in
/-- The outgoing stack slots at a fine vertex are distinct after omitting the
last slot at a source tip, which coincides with the preceding slot. -/
theorem compatibleContourSourceOnly_outgoingVertex_eq_of_live_slots
    (parent : Edge)
    (i j : Fin ((Stack FiniteBank[parent.val,parent.property]).length + 1))
    (live_i : ∀ e : Event, SourceOf[e] = parent.val → i ≠ Fin.last _)
    (live_j : ∀ e : Event, SourceOf[e] = parent.val → j ≠ Fin.last _)
    (equal : Point (EndAt true ⟨FiniteBank[parent.val,parent.property], i⟩ 0) =
      Point (EndAt true ⟨FiniteBank[parent.val,parent.property], j⟩ 0)) : i = j := by
  classical
  let b := FiniteBank[parent.val,parent.property]
  let xs := Stack b
  let atZero (k : Fin (xs.length + 1)) : Time := ⟨⟨b, k⟩, 0⟩
  let atEnd (c : Edge) (k : Fin ((Stack (Sum.inl c)).length + 1)) : Time := ⟨⟨.inl c, k⟩, 1⟩
  let isEnd (t : Time) := ∃ c k, t = atEnd c k
  let vertex (k : Fin (xs.length + 1)) := Point (EndAt true ⟨b, k⟩ 0)
  change vertex i = vertex j at equal
  have nodup_all := K.compatibleContourBankStack_nodup compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour
  have nodup : xs.Nodup := nodup_all b
  have exact_glue := K.compatibleContourSourceOnlyGraft_exact compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W models geometry
  have atZero_inj : Function.Injective atZero := by
    intro k l h
    exact eq_of_heq (Sigma.mk.inj (congrArg Sigma.fst h)).2
  have not_end (k : Fin (xs.length + 1)) (h : isEnd (atZero k)) : False := by
    obtain ⟨c, l, h⟩ := h
    have impossible : (0 : unitInterval) = 1 := eq_of_heq (Sigma.mk.inj h).2
    exact zero_ne_one impossible
  have name_inj (flag : Bool) (k l : Fin (xs.length + 1))
      (h : Named flag ⟨b, k⟩ 0 = Named flag ⟨b, l⟩ 0) : k = l := by
    have h' : (flag, atZero k) = (flag, atZero l) :=
      MetricGluing.bankStackEndpointAddress_injective Stack nodup_all h
    exact atZero_inj (congrArg Prod.snd h')
  have vertex_side (flag : Bool) (k : Fin (xs.length + 1)) :
      vertex k = Point (EndAt flag ⟨b, k⟩ 0) := by
    cases flag
    · exact (MetricGluing.point_eq_of_glue Pieces (glue := Banks) ⟨⟨b, k⟩, 0, rfl, rfl⟩).symm
    · rfl
  have from_cycle {n : ℕ} (H : MetricGluing.BankStackCyclicClass Pieces Stack Base Gap n)
      (c : Fin (n + 1)) (flag : Bool) (k : Fin (xs.length + 1))
      (center : H.center c = EndAt flag ⟨b, k⟩ 0)
      (times : ∀ l, H.time l = atZero k ∨
        (H.time l = atZero (Fin.last xs.length) ∧ ∃ e : Event, SourceOf[e] = parent.val) ∨
          isEnd (H.time l)) (h : vertex k = vertex j) : k = j := by
    have points : Point (H.center 0) = Point (EndAt true ⟨b, j⟩ 0) :=
      (MetricGluing.point_eq_of_eqvGen Pieces (H.related c)).trans
        ((congrArg Point center).trans ((vertex_side flag k).symm.trans h))
    obtain ⟨l, htime⟩ := H.exists_time_eq_of_point_eq exact_glue true (atZero j) points
    rcases times l with matched | ⟨last, e, source⟩ | end_time
    · exact (atZero_inj (htime.trans matched)).symm
    · exact (live_j e source (atZero_inj (htime.trans last))).elim
    · exact (not_end j (htime.symm ▸ end_time)).elim
  have child_of (e : Event) (mem : e ∈ xs) (different : SourceOf[e] ≠ parent.val) :
      ∃ c : Edge, (Fcut).parents.parent c.val = parent.val ∧
        (Fcut).parents.Ancestor SourceOf[e] c.val := by
    have reaches := ((D).mem_contourSavedGapStack Selection contour parent.val e).mp mem
    obtain ⟨c, hc, _⟩ := (Fcut).parents.exists_unique_child_ancestor parent.property reaches different
    exact ⟨c, hc⟩
  have own_last (e : Event) (at_parent : SourceOf[e] = parent.val) : xs.getLast? = some e := by
    obtain ⟨ds, own⟩ := (D).contourSavedGapStack_source_last Selection contour
      (Fcut).boundary_roots starts e
    have shape : xs = ds ++ [e] := by
      change (D).contourSavedGapStack Selection contour parent.val = _
      rw [← at_parent]
      exact own
    rw [shape, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
    rfl
  by_cases empty : xs = []
  · apply Fin.ext
    have hi : i.val < xs.length + 1 := i.isLt
    have hj : j.val < xs.length + 1 := j.isLt
    rw [empty] at hi hj
    simp only [List.length_nil, zero_add] at hi hj
    omega
  by_cases first : i = 0
  · subst i
    obtain ⟨e, tail, head⟩ := List.exists_cons_of_ne_nil empty
    have head_mem : e ∈ xs := head.symm ▸ List.mem_cons_self
    by_cases here : SourceOf[e] = parent.val
    · have no_tail := eq_nil_of_last_named [] tail e (head ▸ nodup) (head ▸ own_last e here)
      have size : xs.length = 1 := by rw [head, no_tail]; rfl
      apply Fin.ext
      have bound : j.val < xs.length + 1 := j.isLt
      have diff : j.val ≠ xs.length := fun eq => live_j e here (Fin.ext eq)
      change 0 = j.val
      omega
    · obtain ⟨child, at_parent, in_child⟩ := child_of e head_mem here
      obtain ⟨A, H, center, _, times, _⟩ :=
        K.exists_compatibleContourSourceOnlyLastChildClass compact nonempty R no_boundary level
          higher M positive inner_disk beta acute contour starts W models parent child at_parent
          e in_child (geometry e) tail head
      apply from_cycle H 0 true 0 center ?_ equal
      intro l
      rw [times]
      exact MetricGluing.BankStackCyclicClass.singleTime_cases _ _ _
        (P := fun t => t = atZero 0 ∨ _ ∨ isEnd t)
        (Or.inr (Or.inr ⟨child, 0, rfl⟩)) (Or.inl rfl)
        (fun r => Or.inr (Or.inr ⟨A.child r, 0, rfl⟩)) l
  by_cases last : i = Fin.last xs.length
  · subst i
    let e := xs.getLast empty
    let before := xs.dropLast
    have shape : xs = before ++ [e] := (List.dropLast_concat_getLast empty).symm
    have mem : e ∈ xs := List.getLast_mem empty
    have different : SourceOf[e] ≠ parent.val := fun h => live_i e h rfl
    obtain ⟨child, at_parent, in_child⟩ := child_of e mem different
    obtain ⟨A, H, center, _, times, _⟩ :=
      K.exists_compatibleContourSourceOnlyFirstChildClass compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W models parent child at_parent
        e in_child (geometry e) before shape
    apply from_cycle H 0 false (Fin.last xs.length) center ?_ equal
    intro l
    rw [times]
    exact MetricGluing.BankStackCyclicClass.singleTime_cases _ _ _
      (P := fun t => t = atZero (Fin.last xs.length) ∨ _ ∨ isEnd t)
      (Or.inl rfl) (Or.inr (Or.inr ⟨child, Fin.last _, rfl⟩))
      (fun r => Or.inr (Or.inr ⟨A.child r, 0, rfl⟩)) l
  have i_pos : 0 < i.val := Nat.pos_of_ne_zero (fun h => first (Fin.ext h))
  have i_bound : i.val < xs.length := by
    have bound : i.val < xs.length + 1 := i.isLt
    have ne : i.val ≠ xs.length := fun h => last (Fin.ext h)
    omega
  obtain ⟨e, f, before, after, shape, left, right⟩ :=
    MetricGluing.bankStack_internal_slot_names (Parameter := ParamAt) Stack b i 0 i_pos i_bound
  change xs = before ++ e :: f :: after at shape
  have e_mem : e ∈ xs := shape.symm ▸ List.mem_append_right _ List.mem_cons_self
  have f_mem : f ∈ xs := shape.symm ▸ List.mem_append_right _ (by simp)
  have e_below : SourceOf[e] ≠ parent.val := by
    intro eq
    have tail_nil := eq_nil_of_last_named before (f :: after) e
      (shape ▸ nodup) (shape ▸ own_last e eq)
    exact List.cons_ne_nil _ _ tail_nil
  obtain ⟨new_child, new_parent, new_inside⟩ := child_of e e_mem e_below
  by_cases tip : SourceOf[f] = parent.val
  · have shape' : xs = (before ++ [e]) ++ f :: after := by
      rw [List.append_assoc]
      exact shape
    have tail_nil := eq_nil_of_last_named (before ++ [e]) after f
      (shape' ▸ nodup) (shape' ▸ own_last f tip)
    have final : xs = before ++ [e, f] := by rw [shape, tail_nil]
    let source : Edge := ⟨SourceOf[f], (D).positiveContourVertex_nonroot Selection contour f⟩
    have same_parent : source = parent := Subtype.ext tip
    have own_stack : Stack (.inl source) = before ++ [e, f] :=
      Eq.mp (congrArg (fun p : Edge => Stack (.inl p) = before ++ [e, f]) same_parent.symm) final
    obtain ⟨A, H, k, _, right_k, _, center, _, times, _⟩ :=
      K.exists_compatibleContourSourceOnlyTipAndChildClass compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts W models f e new_child
        (new_parent.trans tip.symm) new_inside (geometry f) (geometry e) before own_stack
    let atStart (p : Edge) (l : Fin ((Stack (Sum.inl p)).length + 1)) : Time :=
      ⟨⟨.inl p, l⟩, 0⟩
    let P (p : Edge) := ∃ l : Fin ((Stack (Sum.inl p)).length + 1),
      Named true ⟨.inl p, l⟩ 0 = ⟨.inl p, some f, false, 0⟩ ∧
      H.center (Fin.last (A.length + 2)) = EndAt false ⟨.inl p, l⟩ 0 ∧
      ∀ r, H.time r = atStart p l ∨
        H.time r = atStart p (Fin.last (Stack (.inl p)).length) ∨ isEnd (H.time r)
    have at_source : P source := by
      refine ⟨k, right_k, center, ?_⟩
      intro r
      rw [times]
      exact MetricGluing.BankStackCyclicClass.runTime_cases _ _ _ _
        (P := fun t => t = atStart source k ∨
          t = atStart source (Fin.last (Stack (.inl source)).length) ∨ isEnd t)
        (Or.inr (Or.inl rfl)) (Or.inr (Or.inr ⟨new_child, Fin.last _, rfl⟩))
        (Or.inl rfl) (fun q => Or.inr (Or.inr ⟨A.child q, 0, rfl⟩)) r
    obtain ⟨l, right_l, center_l, time_l⟩ := Eq.mp (congrArg P same_parent) at_source
    have named : i = l := name_inj true i l (right.trans right_l.symm)
    subst i
    apply from_cycle H (Fin.last (A.length + 2)) false l center_l ?_ equal
    intro r
    rcases time_l r with first | last | end_time
    · exact Or.inl first
    · exact Or.inr (Or.inl ⟨last, f, tip⟩)
    · exact Or.inr (Or.inr end_time)
  obtain ⟨old_child, old_parent, old_inside⟩ := child_of f f_mem tip
  by_cases same : new_child = old_child
  · subst old_child
    let χ (g : Event) : Bool := decide ((Fcut).parents.Ancestor SourceOf[g] new_child.val)
    have filter_child : xs.filter χ = Stack FiniteBank[new_child.val,new_child.property] := by
      have h := (D).contourSavedGapStack_filter_child Selection contour new_child.val
      rw [new_parent] at h
      exact h
    have selected : Stack FiniteBank[new_child.val,new_child.property] =
        before.filter χ ++ e :: f :: after.filter χ := by
      rw [← filter_child, shape, List.filter_append, List.filter_cons, List.filter_cons]
      have ye : χ e = true := decide_eq_true_eq.mpr new_inside
      have yf : χ f = true := decide_eq_true_eq.mpr old_inside
      rw [ye, yf, if_pos rfl, if_pos rfl]
    obtain ⟨k, l, cls, recover, named_k, _⟩ :=
      K.compatibleContourSourceOnlyChildPair_class compact nonempty R no_boundary level higher
        M positive inner_disk beta acute contour starts W models new_child.val new_child.property
        (by rw [new_parent]; exact parent.property) e f (geometry e) (geometry f)
        (before.filter χ) (after.filter χ) selected
    let P (p : Edge) := ∃ k : Fin ((Stack (Sum.inl p)).length + 1),
      let q : Time := ⟨⟨.inl p, k⟩, 0⟩
      Named false q.1 q.2 = ⟨.inl p, some e, true, 0⟩ ∧
      (∀ x, Relation.EqvGen Banks (L q.1 q.2) x ↔ x = L q.1 q.2 ∨ x = Rgt q.1 q.2) ∧
      (∀ (side other : Bool) (s : Time), EndAt other s.1 s.2 = EndAt side q.1 q.2 →
        s = q ∨ s = atEnd new_child l)
    let p : Edge := ⟨(Fcut).parents.parent new_child.val, by rw [new_parent]; exact parent.property⟩
    have at_p : P p := ⟨k, named_k, cls, fun side other s h => (recover side other s h).2⟩
    obtain ⟨k, named_k, cls, recover⟩ := Eq.mp (congrArg P (Subtype.ext new_parent)) at_p
    have named : i = k := name_inj false i k (left.trans named_k.symm)
    subst i
    have same_points : Point (L ⟨b, k⟩ 0) = Point (EndAt true ⟨b, j⟩ 0) :=
      (vertex_side false k).symm.trans equal
    have endpoints := (cls _).mp (exact_glue _ _ same_points)
    have time : atZero j = atZero k ∨ atZero j = atEnd new_child l := by
      rcases endpoints with hl | hr
      · exact recover false true (atZero j) hl
      · exact recover true true (atZero j) hr
    rcases time with h | h
    · exact (atZero_inj h).symm
    · exact (not_end j ⟨new_child, l, h⟩).elim
  · obtain ⟨A, H, k, _, named_k, center, _, _, times, _⟩ :=
      K.exists_compatibleContourSourceOnlyCrossBlockData compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W models parent old_child new_child
        old_parent new_parent (fun eq => same (Subtype.ext eq.symm)) f e old_inside new_inside
        (geometry f) (geometry e) before after shape
    have named : i = k := name_inj true i k (right.trans named_k.symm)
    subst i
    apply from_cycle H 0 true k center ?_ equal
    intro l
    rw [times]
    exact MetricGluing.BankStackCyclicClass.runTime_cases _ _ _ _
      (P := fun t => t = atZero k ∨ _ ∨ isEnd t)
      (Or.inr (Or.inr ⟨old_child, 0, rfl⟩))
      (Or.inr (Or.inr ⟨new_child, Fin.last _, rfl⟩)) (Or.inl rfl)
      (fun r => Or.inr (Or.inr ⟨A.child r, 0, rfl⟩)) l

end Unfoldings.ConvexRoof
