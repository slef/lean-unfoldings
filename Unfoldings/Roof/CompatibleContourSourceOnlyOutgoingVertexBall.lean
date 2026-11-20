module

public import Unfoldings.Metric.BankStackSlotCases
public import Unfoldings.Roof.CompatibleContourSourceOnlyEmptyStackBall
public import Unfoldings.Roof.CompatibleContourSourceOnlyEmptyStackLeafBall
public import Unfoldings.Roof.CompatibleContourSourceOnlyChildPairBall
public import Unfoldings.Roof.CompatibleContourSourceOnlyCrossBlockBall
public import Unfoldings.Roof.CompatibleContourSourceOnlyFirstChildBall
public import Unfoldings.Roof.CompatibleContourSourceOnlyLastChildBall
public import Unfoldings.Roof.CompatibleContourSourceOnlyTipAndChildBall
public import Unfoldings.Roof.CompatibleContourSourceOnlySingleTipBall

/-! Every seam at the lower endpoint of a finite parent bank has a planar ball. -/

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

local instance sourceOnlyOutgoingVertexBallIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlyOutgoingVertexBallWholeFintype : Fintype W.Index := W.finiteIndex

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
local notation "Addr" => MetricGluing.BankStackAddress (G := Event) (Parameter := ParamAt)
local notation "Named" => MetricGluing.bankStackEndpointAddress (Parameter := ParamAt) Stack
local notation "Mark" => MetricGluing.bankStackAddressPoint Stack Pieces Base Gap
local notation "Valid" => MetricGluing.BankStackAddressValid Stack
local notation "EndAt" => MetricGluing.bankStackEndpoint Stack Pieces Base Gap
local notation "L" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Rgt" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams L Rgt
local notation "Time" => (Σ s : MetricGluing.BankStackSlot Stack, ParamAt (Sigma.fst s))

local notation "BankAt[" e "]" => K.compatibleContourSourceBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "MovedAt[" e "]" => K.compatibleContourSourceOnlyBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e


local notation "Edge" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Interval[" v "," h "]" => TriangleComplex.contourParentInterval
  D Selection contour (PotentialCutForest.boundary_roots Fcut) starts v h
local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W
local notation "Retain" => PotentialCutForest.retain Fcut
local notation "SourceOf[" e "]" => TriangleComplex.positiveContourVertex D Selection contour e
local notation "RoofPoint[" j "]" => (Sigma.mk none (Map
  (TriangleComplex.vertexPoint D Retain (TriangleComplex.boundaryEndVertex D Retain
    (PairedInvolutions.System.Chain.point (TriangleComplex.BoundaryContour.cycle contour) j)))) :
      MetricGluing.Total Pieces)

local notation "Point" => MetricGluing.point Pieces Banks
local notation "LengthAt[" e "]" => TriangleComplex.positiveContourBankLength D Selection contour e
local notation "SourceEdge[" e "]" => FiniteBank[SourceOf[e],
  TriangleComplex.positiveContourVertex_nonroot D Selection contour e]

omit beta acute in
private theorem eq_nil_of_last_named {G : Type*} (before after : List G) (g : G)
    (nodup : (before ++ g :: after).Nodup)
    (last : (before ++ g :: after).getLast? = some g) : after = [] := by
  by_contra hn
  rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
    List.getLast?_cons_of_ne_nil hn] at last
  exact (List.nodup_cons.mp (List.nodup_append'.mp nodup).2.1).1
    (List.mem_of_mem_getLast? (last.symm ▸ (show g ∈ (some g : Option G) by simp)))

set_option maxHeartbeats 4200000 in
-- The cases transport dependent slot labels across the original fan chart constructions.
/-- Every stack seam at the start of an original finite parent bank has a whole planar ball. -/
theorem compatibleContourSourceOnly_outgoingVertex_planarBall
    (ends : (D).contourOriginalVertex Selection contour (Fin.last contour.length) ∈
      (Fcut).parents.roots)
    (parent : Edge)
    (strict : ∀ (e : Event) (k : Fin LengthAt[e]), let B := BankAt[e]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ))
    (i : Fin ((Stack FiniteBank[parent.val,parent.property]).length + 1)) :
    HasMetricBallChart ℂ (Point (EndAt true ⟨FiniteBank[parent.val,parent.property], i⟩ 0)) := by
  classical
  let b := FiniteBank[parent.val,parent.property]
  let xs := Stack b
  let chart (j : Fin (xs.length + 1)) := HasMetricBallChart ℂ (Point (EndAt true ⟨b, j⟩ 0))
  have nodup : xs.Nodup := K.compatibleContourBankStack_nodup compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour b
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
  have actual_source (e : Event) (at_parent : SourceOf[e] = parent.val) : b = SourceEdge[e] := by
    apply congrArg Sum.inl
    exact Subtype.ext at_parent.symm
  have at_tip (e : Event) (at_parent : SourceOf[e] = parent.val) (mem : e ∈ xs)
      (j : Fin (xs.length + 1)) (side flag : Bool)
      (name : Named side ⟨b, j⟩ 0 = ⟨b, some e, flag, 0⟩)
      (tip_chart : HasMetricBallChart ℂ (Point ⟨some e, (models e).edgePoint false 0 0⟩)) :
      chart j := by
    have mark := MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap
      side (⟨⟨b, j⟩, 0⟩ : Time) b e mem flag 0 name
    let source : Edge := ⟨SourceOf[e], (D).positiveContourVertex_nonroot Selection contour e⟩
    have on_source (p : Edge) (same : p = source) (member : e ∈ Stack (.inl p)) :
        Gap (.inl p) e member flag 0 = (models e).edgePoint false 0 0 := by
      subst p
      exact K.compatibleContourSourceOnlyGapMark_at_source compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts models e (geometry e) member flag
    have gap_at_source := on_source parent (Subtype.ext at_parent.symm) mem
    have same : EndAt side ⟨b, j⟩ 0 = ⟨some e, (models e).edgePoint false 0 0⟩ :=
      mark.trans (congrArg (Sigma.mk (some e)) gap_at_source)
    have eqv : Point (EndAt false ⟨b, j⟩ 0) = Point (EndAt true ⟨b, j⟩ 0) :=
      MetricGluing.point_eq_of_glue Pieces (glue := Banks) ⟨⟨b, j⟩, 0, rfl, rfl⟩
    change HasMetricBallChart ℂ (Point (EndAt true ⟨b, j⟩ 0))
    cases side
    · rw [← eqv, same]
      exact tip_chart
    · rw [same]
      exact tip_chart
  have source_chart (e : Event) (at_parent : SourceOf[e] = parent.val)
      (only : xs = [e]) : HasMetricBallChart ℂ (Point ⟨some e, (models e).edgePoint false 0 0⟩) := by
    apply K.compatibleContourSourceOnlySingleTip_planarBall compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W geometry e
    exact (actual_source e at_parent) ▸ only
  have transfer_pair (j k : Fin (xs.length + 1)) (s : Bool)
      (same : Named s ⟨b, j⟩ 0 = Named s ⟨b, k⟩ 0)
      (from_k : HasMetricBallChart ℂ (Point (EndAt s ⟨b, k⟩ 0))) : chart j := by
    have same_tag := MetricGluing.bankStackEndpoint_eq_of_same_address Stack Pieces Base Gap s s
      (⟨⟨b, j⟩, 0⟩ : Time) (⟨⟨b, k⟩, 0⟩ : Time) same
    have eqv : Point (EndAt false ⟨b, j⟩ 0) = Point (EndAt true ⟨b, j⟩ 0) :=
      MetricGluing.point_eq_of_glue Pieces (glue := Banks) ⟨⟨b, j⟩, 0, rfl, rfl⟩
    change HasMetricBallChart ℂ (Point (EndAt true ⟨b, j⟩ 0))
    cases s
    · rw [← eqv, same_tag]
      exact from_k
    · rw [same_tag]
      exact from_k
  change chart i
  by_cases empty : xs = []
  · have i0 : i = 0 := by
      apply Fin.ext
      have bound := i.isLt
      change i.val < xs.length + 1 at bound
      rw [empty] at bound
      simp only [List.length_nil, zero_add] at bound
      change i.val = 0
      omega
    rw [i0]
    let A := (D).contourFullParentWedgeRun Selection contour (Fcut).boundary_roots starts parent
    rcases Nat.eq_zero_or_pos A.length with leaf | many
    · exact K.compatibleContourSourceOnlyEmptyStack_leaf_planarBall compact nonempty R
        no_boundary level higher M positive inner_disk beta acute contour starts W geometry ends
        parent empty leaf
    · exact K.compatibleContourSourceOnlyEmptyStack_multiple_planarBall compact nonempty R
        no_boundary level higher M positive inner_disk beta acute contour starts W geometry ends
        parent empty many
  by_cases first : i = 0
  · rw [first]
    obtain ⟨e, tail, head⟩ := List.exists_cons_of_ne_nil empty
    have head_mem : e ∈ xs := head.symm ▸ List.mem_cons_self
    by_cases here : SourceOf[e] = parent.val
    · have no_tail : tail = [] := eq_nil_of_last_named [] tail e
        (head ▸ nodup) (head ▸ own_last e here)
      have shape : xs = [e] := head.trans (congrArg (List.cons e) no_tail)
      exact at_tip e here head_mem 0 true false
        (MetricGluing.bankStack_first_gap_addresses Stack b 0 e tail head).2
        (source_chart e here shape)
    · obtain ⟨c, at_c, inside⟩ := child_of e head_mem here
      exact K.compatibleContourSourceOnlyLastChild_planarBall compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts W geometry parent c at_c e
        inside tail head (strict e)
  by_cases last : i = Fin.last xs.length
  · rw [last]
    let e := xs.getLast empty
    let before := xs.dropLast
    have shape : xs = before ++ [e] := (List.dropLast_concat_getLast empty).symm
    have mem : e ∈ xs := List.getLast_mem empty
    by_cases here : SourceOf[e] = parent.val
    · have only_tip : HasMetricBallChart ℂ (Point ⟨some e, (models e).edgePoint false 0 0⟩) := by
        cases hb : before.reverse with
        | nil =>
          have empty_before : before = [] := (List.reverse_eq_nil_iff.mp hb)
          exact source_chart e here (shape.trans (by rw [empty_before]; rfl))
        | cons g tail =>
          have named_before : before = tail.reverse ++ [g] := by
            have h := congrArg List.reverse hb
            simpa only [List.reverse_reverse, List.reverse_cons] using h
          have whole : xs = tail.reverse ++ [g, e] := by
            rw [shape, named_before, List.append_assoc]
            rfl
          have gmem : g ∈ xs := whole.symm ▸ List.mem_append_right _ (by simp)
          have different : SourceOf[g] ≠ parent.val := by
            intro eq
            have same : g = e := (D).positiveContourVertex_injective Selection contour
              (Fcut).boundary_roots starts (eq.trans here.symm)
            have inner := (List.nodup_append'.mp (whole ▸ nodup)).2.1
            exact (List.nodup_cons.mp inner).1 (same.symm ▸ List.mem_cons_self)
          obtain ⟨c, at_c, inside⟩ := child_of g gmem different
          exact K.compatibleContourSourceOnlyTipAndChild_planarBall compact nonempty R no_boundary
            level higher M positive inner_disk beta acute contour starts W geometry e g c
            (at_c.trans here.symm) inside tail.reverse ((actual_source e here) ▸ whole) (strict g)
      exact at_tip e here mem (Fin.last xs.length) false true
        (MetricGluing.bankStack_last_gap_addresses Stack b 0 e before shape).1 only_tip
    · obtain ⟨c, at_c, inside⟩ := child_of e mem here
      have from_last := K.compatibleContourSourceOnlyFirstChild_planarBall_of_complete_contour
        compact nonempty R no_boundary level higher M positive inner_disk beta acute contour starts
        W geometry ends parent c at_c e inside before shape (strict e)
      exact transfer_pair (Fin.last xs.length) (Fin.last xs.length) false rfl from_last
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
  obtain ⟨first_child, first_parent, first_inside⟩ := child_of e e_mem e_below
  by_cases tip : SourceOf[f] = parent.val
  · have shape' : xs = (before ++ [e]) ++ f :: after := by
      rw [List.append_assoc]
      exact shape
    have tail_nil := eq_nil_of_last_named (before ++ [e]) after f
      (shape' ▸ nodup) (shape' ▸ own_last f tip)
    have final : xs = before ++ [e, f] := by rw [shape, tail_nil]
    have at_source : Stack SourceEdge[f] = before ++ [e, f] :=
      Eq.mp (congrArg (fun x => Stack x = before ++ [e, f]) (actual_source f tip)) final
    have source_chart := K.compatibleContourSourceOnlyTipAndChild_planarBall compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W geometry f e
      first_child (first_parent.trans tip.symm) first_inside before at_source (strict e)
    exact at_tip f tip f_mem i true false right source_chart
  obtain ⟨second_child, second_parent, second_inside⟩ := child_of f f_mem tip
  by_cases same : first_child = second_child
  · subst second_child
    let χ (g : Event) : Bool := decide ((Fcut).parents.Ancestor SourceOf[g] first_child.val)
    have filter_child : xs.filter χ = Stack FiniteBank[first_child.val,first_child.property] := by
      have h := (D).contourSavedGapStack_filter_child Selection contour first_child.val
      rw [first_parent] at h
      exact h
    have selected : Stack FiniteBank[first_child.val,first_child.property] =
        before.filter χ ++ e :: f :: after.filter χ := by
      rw [← filter_child, shape, List.filter_append, List.filter_cons, List.filter_cons]
      have ye : χ e = true := decide_eq_true_eq.mpr first_inside
      have yf : χ f = true := decide_eq_true_eq.mpr second_inside
      rw [ye, yf, if_pos rfl, if_pos rfl]
    obtain ⟨k, e_named, _, middle⟩ := K.compatibleContourSourceOnlyChildPair_planarBall
      compact nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W
      geometry first_child.val first_child.property
      (by rw [first_parent]; exact parent.property) e f
      (before.filter χ) (after.filter χ) selected strict
    let HasPair (p : Edge) := ∃ k : Fin ((Stack FiniteBank[p.val,p.property]).length + 1),
      Named false ⟨FiniteBank[p.val,p.property], k⟩ 0 =
        ⟨FiniteBank[p.val,p.property], some e, true, 0⟩ ∧
      HasMetricBallChart ℂ (Point (L ⟨FiniteBank[p.val,p.property], k⟩ 0))
    let p : Edge := ⟨(Fcut).parents.parent first_child.val, by rw [first_parent]; exact parent.property⟩
    have original : HasPair p := ⟨k, e_named, middle⟩
    have parent_tag : p = parent := Subtype.ext first_parent
    obtain ⟨j, at_j, chart_j⟩ := Eq.mp (congrArg HasPair parent_tag) original
    exact transfer_pair i j false (left.trans at_j.symm) chart_j
  · obtain ⟨k, _, f_named, middle⟩ := K.compatibleContourSourceOnlyCrossBlock_planarBall
      compact nonempty R no_boundary level higher M positive inner_disk beta acute contour starts
      W geometry parent second_child first_child second_parent first_parent
      (fun eq => same (Subtype.ext eq.symm)) f e second_inside first_inside strict before after shape
    exact transfer_pair i k true (right.trans f_named.symm) middle

end Unfoldings.ConvexRoof
