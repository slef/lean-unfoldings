module

public import Unfoldings.FewestNets.ThreeExitGraftEmptyStackBall
public import Unfoldings.FewestNets.ThreeExitGraftEmptyStackLeafBall
public import Unfoldings.FewestNets.ThreeExitGraftChildPairBall
public import Unfoldings.FewestNets.ThreeExitGraftCrossBlockBall
public import Unfoldings.FewestNets.ThreeExitGraftFirstChildBall
public import Unfoldings.FewestNets.ThreeExitGraftLastChildBall
public import Unfoldings.FewestNets.ThreeExitGraftTipAndChildBall
public import Unfoldings.FewestNets.ThreeExitGraftSingleTipBall
public import Unfoldings.FewestNets.ThreeExitGraftVertexAttachments
public import Unfoldings.FewestNets.ThreeExitGraftVertexFiber
public import Unfoldings.FewestNets.ThreeExitGraftOriginalNet
public import Unfoldings.Metric.BankStackSlotCases




/-! The finite vertex sectors complete the whole flat graft. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel

open MetricGluing

universe u v

set_option maxHeartbeats 1800000

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : FewestNets.ThreeExitStemWindows}
  {R : K.ThreeExitComponentRouting seed B compact nonempty H}

local notation "U" => K.selectionComponent slopes seed
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ K.restrictedCarrier U}
local notation "G" => SlopeEnvelope.recenter
  (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty) B.reference
local notation "pointOf" => (fun v : V => K.projectedVertex (Subtype.val v))

variable {level : ℝ}
  {M : (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel}
  (L : R.FloorWindowModel level M)

local notation "T[" h "]" => R.fineMesh level M h
local notation "D[" h "]" => SpatialEnvelope.FloorMesh.pairedComplex T[h]
local notation "F[" h "]" => R.fineMeshForest level M h
local notation "Sel[" h "]" => PotentialCutForest.selection F[h]

local instance graftFlatnessIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
    Fintype (T[h]).Index := @Fintype.ofFinite _ (T[h]).finite

variable (S : SourceContour (R := R) (M := M) (level := level))

local notation "T" => T[S.higher]
local notation "D" => D[S.higher]
local notation "Fcut" => F[S.higher]
local notation "Selection" => Sel[S.higher]
local notation "Event" => TriangleComplex.PositiveContourSource D Selection S.contour
local notation "Model[" e "]" => OrientedBankGap.model (S.gaps e)
local notation "Pieces" => polygonalBankStackPiece L.whole.Cut (fun e : Event => BankGapModel.region (Model[e]))
local notation "Stack" => PotentialCutForest.contourAttachmentStack Fcut S.contour
local notation "Base" => contourBaseMark L S
local notation "Gap" => PotentialCutForest.contourGapMark Fcut S.contour S.starts
  (fun e : Event => Model[e])
local notation "Attachment" => PotentialCutForest.ContourAttachment Fcut
local notation "Param" => PotentialCutForest.contourAttachmentParameter Fcut

local notation "Edge" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "FiniteBank[" v "," h "]" => (Sum.inl (Subtype.mk v h) : Attachment)
local notation "Retain" => PotentialCutForest.retain Fcut
local notation "Map" => L.fineMeshWholeMap S.higher
local notation "RoofPoint[" j "]" => (Sigma.mk none (Map
  (TriangleComplex.vertexPoint D Retain (TriangleComplex.boundaryEndVertex D Retain
    (PairedInvolutions.System.Chain.point (TriangleComplex.BoundaryContour.cycle S.contour) j)))) :
      MetricGluing.Total Pieces)
local notation "Interval[" v "," h "]" => TriangleComplex.contourParentInterval
  D Selection S.contour (PotentialCutForest.boundary_roots Fcut) S.starts v h
local notation "RoofTime" => MetricGluing.bankStackRoofTime (Parameter := Param) Stack
local notation "Germ" => contourFiniteRoofGerm S
local notation "EndAt" => MetricGluing.bankStackEndpoint Stack Pieces Base Gap
local notation "Time" => (Σ s : MetricGluing.BankStackSlot Stack, Param (Sigma.fst s))

local notation "Named" => MetricGluing.bankStackEndpointAddress (Parameter := Param) Stack
local notation "Addr" => MetricGluing.BankStackAddress («G» := Event) (Parameter := Param)
local notation "Valid" => MetricGluing.BankStackAddressValid Stack
local notation "Mark" => MetricGluing.bankStackAddressPoint Stack Pieces Base Gap
local notation "SourceOf[" e "]" => TriangleComplex.positiveContourVertex D Selection S.contour e
local notation "SourceEdge[" e "]" => (Sum.inl (Subtype.mk SourceOf[e]
  (TriangleComplex.positiveContourVertex_nonroot D Selection S.contour e)) : Attachment)
local notation "BankAt[" e "]" => PotentialCutForest.contourSourceRay Fcut S.contour S.starts e
local notation "MovedAt[" e "]" => PotentialCutForest.contourSourceOpenedRay Fcut S.contour S.starts e
local notation "models" => (fun e : Event => Model[e])
local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams Left Right
local notation "Point" => MetricGluing.point Pieces Banks
local notation "geometry" => S.gaps

local notation "LengthAt[" e "]" => TriangleComplex.positiveContourBankLength D Selection S.contour e
local notation "Visit[" i "]" => TriangleComplex.contourOriginalVertex D Selection S.contour i
local notation "Exit" => TriangleComplex.ContourTerminalEdge D Selection
local notation "Graft" => contourGraft L S

private theorem eq_nil_of_last_named {Item : Type*} (before after : List Item) (g : Item)
    (nodup : (before ++ g :: after).Nodup)
    (last : (before ++ g :: after).getLast? = some g) : after = [] := by
  by_contra hn
  rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
    List.getLast?_cons_of_ne_nil hn] at last
  exact (List.nodup_cons.mp (List.nodup_append'.mp nodup).2.1).1
    (List.mem_of_mem_getLast? (last.symm ▸ (show g ∈ (some g : Option Item) by simp)))

set_option maxHeartbeats 4200000 in
-- The cases transport dependent slot labels across the original fan chart constructions.
/-- Every stack seam at the start of an original finite parent bank has a whole planar ball. -/
theorem contourGraft_outgoingVertex_planarBall
    (ends : (D).contourOriginalVertex Selection S.contour (Fin.last S.contour.length) ∈
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
  have nodup : xs.Nodup := contourGraft_stack_nodup S b
  have child_of (e : Event) (mem : e ∈ xs) (different : SourceOf[e] ≠ parent.val) :
      ∃ c : Edge, (Fcut).parents.parent c.val = parent.val ∧
        (Fcut).parents.Ancestor SourceOf[e] c.val := by
    have reaches := ((D).mem_contourSavedGapStack Selection S.contour parent.val e).mp mem
    obtain ⟨c, hc, _⟩ := (Fcut).parents.exists_unique_child_ancestor parent.property reaches different
    exact ⟨c, hc⟩
  have own_last (e : Event) (at_parent : SourceOf[e] = parent.val) : xs.getLast? = some e := by
    obtain ⟨ds, own⟩ := (D).contourSavedGapStack_source_last Selection S.contour
      (Fcut).boundary_roots S.starts e
    have shape : xs = ds ++ [e] := by
      change (D).contourSavedGapStack Selection S.contour parent.val = _
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
    let source : Edge := ⟨SourceOf[e], (D).positiveContourVertex_nonroot Selection S.contour e⟩
    have on_source (p : Edge) (same : p = source) (member : e ∈ Stack (.inl p)) :
        Gap (.inl p) e member flag 0 = (models e).edgePoint false 0 0 := by
      subst p
      exact (Fcut).contourGapMark_at_source S.contour S.starts S.gaps e member flag
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
    apply L.contourGraftSingleTip_planarBall S e
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
    let A := (D).contourFullParentWedgeRun Selection S.contour (Fcut).boundary_roots S.starts parent
    rcases Nat.eq_zero_or_pos A.length with leaf | many
    · exact L.contourGraftEmptyStack_leaf_planarBall S ends
        parent empty leaf
    · exact L.contourGraftEmptyStack_multiple_planarBall S ends
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
      exact L.contourGraftLastChild_planarBall S parent c at_c e
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
            have same : g = e := (D).positiveContourVertex_injective Selection S.contour
              (Fcut).boundary_roots S.starts (eq.trans here.symm)
            have inner := (List.nodup_append'.mp (whole ▸ nodup)).2.1
            exact (List.nodup_cons.mp inner).1 (same.symm ▸ List.mem_cons_self)
          obtain ⟨c, at_c, inside⟩ := child_of g gmem different
          exact L.contourGraftTipAndChild_planarBall S e g c
            (at_c.trans here.symm) inside tail.reverse ((actual_source e here) ▸ whole) (strict g)
      exact at_tip e here mem (Fin.last xs.length) false true
        (MetricGluing.bankStack_last_gap_addresses Stack b 0 e before shape).1 only_tip
    · obtain ⟨c, at_c, inside⟩ := child_of e mem here
      have from_last := L.contourGraftFirstChild_planarBall_of_complete_contour S ends parent c at_c e inside before shape (strict e)
      exact transfer_pair (Fin.last xs.length) (Fin.last xs.length) false rfl from_last
  have i_pos : 0 < i.val := Nat.pos_of_ne_zero (fun h => first (Fin.ext h))
  have i_bound : i.val < xs.length := by
    have bound : i.val < xs.length + 1 := i.isLt
    have ne : i.val ≠ xs.length := fun h => last (Fin.ext h)
    omega
  obtain ⟨e, f, before, after, shape, left, right⟩ :=
    MetricGluing.bankStack_internal_slot_names (Parameter := Param) Stack b i 0 i_pos i_bound
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
    have source_chart := L.contourGraftTipAndChild_planarBall S f e
      first_child (first_parent.trans tip.symm) first_inside before at_source (strict e)
    exact at_tip f tip f_mem i true false right source_chart
  obtain ⟨second_child, second_parent, second_inside⟩ := child_of f f_mem tip
  by_cases same : first_child = second_child
  · subst second_child
    let χ (g : Event) : Bool := decide ((Fcut).parents.Ancestor SourceOf[g] first_child.val)
    have filter_child : xs.filter χ = Stack FiniteBank[first_child.val,first_child.property] := by
      have h := (D).contourSavedGapStack_filter_child Selection S.contour first_child.val
      rw [first_parent] at h
      exact h
    have selected : Stack FiniteBank[first_child.val,first_child.property] =
        before.filter χ ++ e :: f :: after.filter χ := by
      rw [← filter_child, shape, List.filter_append, List.filter_cons, List.filter_cons]
      have ye : χ e = true := decide_eq_true_eq.mpr first_inside
      have yf : χ f = true := decide_eq_true_eq.mpr second_inside
      rw [ye, yf, ite_eq_left rfl, ite_eq_left rfl]
    obtain ⟨k, e_named, _, middle⟩ := L.contourGraftChildPair_planarBall S first_child.val first_child.property
      (by rw [first_parent]; exact parent.property) e f
      (before.filter χ) (after.filter χ) selected strict
    let HasPair (p : Edge) := ∃ k : Fin ((Stack FiniteBank[p.val,p.property]).length + 1),
      Named false ⟨FiniteBank[p.val,p.property], k⟩ 0 =
        ⟨FiniteBank[p.val,p.property], some e, true, 0⟩ ∧
      HasMetricBallChart ℂ (Point (Left ⟨FiniteBank[p.val,p.property], k⟩ 0))
    let p : Edge := ⟨(Fcut).parents.parent first_child.val, by rw [first_parent]; exact parent.property⟩
    have original : HasPair p := ⟨k, e_named, middle⟩
    have parent_tag : p = parent := Subtype.ext first_parent
    obtain ⟨j, at_j, chart_j⟩ := Eq.mp (congrArg HasPair parent_tag) original
    exact transfer_pair i j false (left.trans at_j.symm) chart_j
  · obtain ⟨k, _, f_named, middle⟩ := L.contourGraftCrossBlock_planarBall S parent second_child first_child second_parent first_parent
      (fun eq => same (Subtype.ext eq.symm)) f e second_inside first_inside strict before after shape
    exact transfer_pair i k true (right.trans f_named.symm) middle


/-- The finite window covers both endpoints of every original finite seam. -/
theorem contourGraft_finiteVertex_planarBall
    (ends : Visit[Fin.last S.contour.length] ∈ (Fcut).parents.roots)
    (strict : ∀ (e : Event) (k : Fin LengthAt[e]), let bank := BankAt[e]
      0 < inner ℝ (bank.chain.vertex k.succ.castSucc - bank.start) (bank.chain.edge k.succ))
    (e : Edge) (i : Fin ((Stack (.inl e)).length + 1)) (t : unitInterval)
    (endpoint : t = 0 ∨ t = 1) :
    HasMetricBallChart ℂ (Point (Left ⟨.inl e, i⟩ t)) := by
  classical
  rcases endpoint with rfl | rfl
  · have glue : Point (Left ⟨.inl e, i⟩ 0) = Point (Right ⟨.inl e, i⟩ 0) :=
      point_eq_of_glue Pieces ⟨⟨.inl e, i⟩, 0, rfl, rfl⟩
    rw [glue]
    exact L.contourGraft_outgoingVertex_planarBall S ends e strict i
  · by_cases root : (Fcut).parents.parent e.val ∈ (Fcut).parents.roots
    · let exit : Exit := ⟨e.val, e.property, root⟩
      have same := L.contourGraft_terminalJoin_endpoint S exit i false
      change Left ⟨.inl e, i⟩ 1 = Left ⟨.inr exit, i⟩ 0 at same
      rw [same]
      exact L.contourGraft_terminalJoin_planarBall S exit i
    · have joined := if empty : Stack (.inl e) = [] then
        L.contourGraftFiniteEnd_empty_eq_outgoing S e root empty i
      else L.contourGraftFiniteEnd_nonempty_eq_outgoing S e root empty i
      obtain ⟨k, eq⟩ := joined
      rw [eq]
      exact L.contourGraft_outgoingVertex_planarBall S ends ⟨_, root⟩ strict k

/-- The entire unbounded graft develops isometrically onto the plane. -/
theorem exists_contourGraft_surjective_isometry
    (ends : Visit[Fin.last S.contour.length] ∈ (Fcut).parents.roots)
    (strict : ∀ (e : Event) (k : Fin LengthAt[e]), let bank := BankAt[e]
      0 < inner ℝ (bank.chain.vertex k.succ.castSucc - bank.start) (bank.chain.edge k.succ)) :
    ∃ develop : Graft → Plane, Isometry develop ∧ Function.Surjective develop :=
  L.exists_contourGraft_isometry_of_local_charts S
    (L.contourGraft_hasMetricBallChart_of_finite_vertices S (L.contourGraft_finiteVertex_planarBall S ends strict))
    (L.contourGraftCollapse_fiber_of_vertex S)

include L in
/-- The checked source contour gives a net on the input edges of the selected component. -/
theorem hasOriginalEdgeNet_of_complete_contour
    (selected : K.normalSlope seed ∈ slopes)
    (ends : Visit[Fin.last S.contour.length] ∈ (Fcut).parents.roots)
    (strict : ∀ (e : Event) (k : Fin LengthAt[e]), let bank := BankAt[e]
      0 < inner ℝ (bank.chain.vertex k.succ.castSucc - bank.start) (bank.chain.edge k.succ)) :
    C.HasOriginalEdgeNet U := by
  obtain ⟨develop, rigid, onto⟩ := L.exists_contourGraft_surjective_isometry S ends strict
  exact L.hasOriginalEdgeNet_of_contourGraft_isometry S selected develop rigid onto

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
