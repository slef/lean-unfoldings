module

public import Unfoldings.FewestNets.ThreeExitGraftChildPairClasses
public import Unfoldings.FewestNets.ThreeExitGraftWedgeEndpoints
public import Unfoldings.Complex.ContourChildBlockWedgeRun
public import Unfoldings.Metric.BankStackCyclicClass


/-! The cyclic class between two different child subtrees. -/

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

local instance graftCrossBlockClassesIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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
/-- A named bend keeps both original slot incidences under a different parent label. -/
theorem contourGraftGapBend_endpoint_transfer_of_parent
    (child parent : Edge) (parent_eq : (Fcut).parents.parent child.val = parent.val)
    (e : Event) (g : OrientedBankGap BankAt[e] MovedAt[e])
    (i : Fin ((Stack FiniteBank[parent.val,parent.property]).length + 1))
    (j : Fin ((Stack FiniteBank[child.val,child.property]).length + 1)) (side flag : Bool)
    (outgoing : Named side ⟨FiniteBank[parent.val,parent.property], i⟩ 0 =
      ⟨FiniteBank[parent.val,parent.property], some e, flag, 0⟩)
    (incoming : Named side ⟨FiniteBank[child.val,child.property], j⟩ 1 =
      ⟨FiniteBank[child.val,child.property], some e, flag, 1⟩) :
    let first : Time := ⟨⟨FiniteBank[parent.val,parent.property], i⟩, 0⟩
    let second : Time := ⟨⟨FiniteBank[child.val,child.property], j⟩, 1⟩
    EndAt side first.1 first.2 = EndAt side second.1 second.2 ∧
      ∀ (other : Bool) (p : Time), EndAt other p.1 p.2 = EndAt side first.1 first.2 →
        other = side ∧ (p = first ∨ p = second) := by
  obtain ⟨parent, nonroot⟩ := parent
  change (Fcut).parents.parent child.val = parent at parent_eq
  subst parent
  exact L.contourGraftGapBend_endpoint_transfer S child.val child.property
    nonroot e g i j side flag outgoing incoming

/-- At a cross-block adjacency, two gap bends and the intervening original roof wedges
form precisely one cyclic seam class, in the original S.contour order. -/
theorem exists_contourGraftCrossBlockData
    (parent old_child new_child : Edge)
    (old_parent : (Fcut).parents.parent old_child.val = parent.val)
    (new_parent : (Fcut).parents.parent new_child.val = parent.val)
    (different : old_child.val ≠ new_child.val) (old new : Event)
    (old_in : (Fcut).parents.Ancestor SourceOf[old] old_child.val)
    (new_in : (Fcut).parents.Ancestor SourceOf[new] new_child.val)
    (old_gap : OrientedBankGap BankAt[old] MovedAt[old])
    (new_gap : OrientedBankGap BankAt[new] MovedAt[new])
    (pre post : List Event)
    (adjacent : Stack FiniteBank[parent.val,parent.property] = pre ++ new :: old :: post) :
    let initial := finRotate (S.contour.length + 1) (Interval[old_child.val,old_child.property]).leave
    let final := (Interval[new_child.val,new_child.property]).enter
    let above := FiniteBank[parent.val,parent.property]
    ∃ (A : (D).ContourParentWedgeRun Selection S.contour (Fcut).boundary_roots S.starts
        parent.val initial final)
      (H : MetricGluing.BankStackCyclicClass Pieces Stack Base Gap (A.length + 2))
      (slot : Fin ((Stack above).length + 1)),
      Named false ⟨above, slot⟩ 0 = ⟨above, some new, true, 0⟩ ∧
      Named true ⟨above, slot⟩ 0 = ⟨above, some old, false, 0⟩ ∧
      H.center 0 = EndAt true ⟨above, slot⟩ 0 ∧
      H.center (Fin.last (A.length + 2)) = EndAt false ⟨above, slot⟩ 0 ∧
      (∀ i : Fin (A.length + 1), H.center i.castSucc.succ = RoofPoint[A.visit i]) ∧
      H.time = MetricGluing.BankStackCyclicClass.runTime
        (⟨⟨FiniteBank[old_child.val,old_child.property], 0⟩, 1⟩ : Time)
        ⟨⟨FiniteBank[new_child.val,new_child.property],
          Fin.last (Stack FiniteBank[new_child.val,new_child.property]).length⟩, 1⟩
        ⟨⟨above, slot⟩, 0⟩
        (fun j => ⟨⟨FiniteBank[(A.child j).val,(A.child j).property], 0⟩, 1⟩) ∧
      H.side = MetricGluing.BankStackCyclicClass.runSide ∧
      (∀ i, Stack FiniteBank[(A.child i).val,(A.child i).property] = []) ∧
      (∀ j : Fin (S.contour.length + 1), (∃ i, A.visit i = j) ↔
        (D).contourOriginalVertex Selection S.contour j = parent.val ∧
          j ≠ (Interval[parent.val,parent.property]).leave ∧
            old.val.val ≤ j.val ∧ j.val < new.val.val) ∧
      Function.Injective H.center := by
  obtain ⟨A, ⟨older, old_shape⟩, ⟨newer, new_shape⟩, empty, interval⟩ :=
    (D).exists_contourChildBlockWedgeRun Selection S.contour (Fcut).boundary_roots S.starts
      parent.val parent.property old_child new_child old_parent new_parent different old new
      old_in new_in pre post adjacent
  let a := FiniteBank[old_child.val,old_child.property]
  let b := FiniteBank[new_child.val,new_child.property]
  let above := FiniteBank[parent.val,parent.property]
  let last := Fin.last (Stack b).length
  let first_time : Time := ⟨⟨a, 0⟩, 1⟩
  let last_time : Time := ⟨⟨b, last⟩, 1⟩
  let at_edge (e : Edge) := FiniteBank[e.val,e.property]
  let roof (i : Fin (A.length + 1)) := RoofPoint[A.visit i]
  let times (i : Fin A.length) : Time := ⟨⟨at_edge (A.child i), 0⟩, 1⟩
  have old_shape' : Stack a = old :: older := old_shape
  have new_shape' : Stack b = newer ++ [new] := new_shape
  obtain ⟨slot, new_out, old_out⟩ := MetricGluing.bankStack_exists_adjacent_gap_slot
    (Parameter := Param) Stack above 0 adjacent
  let closing : Time := ⟨⟨above, slot⟩, 0⟩
  let old_center := EndAt true closing.1 closing.2
  let new_center := EndAt false closing.1 closing.2
  have old_entry := (MetricGluing.bankStack_first_gap_addresses (Parameter := Param)
    Stack a 1 old older old_shape').2
  have new_entry := (MetricGluing.bankStack_last_gap_addresses (Parameter := Param)
    Stack b 1 new newer new_shape').1
  obtain ⟨hold, iold⟩ := L.contourGraftGapBend_endpoint_transfer_of_parent S old_child parent
    old_parent old old_gap slot 0 true false old_out old_entry
  obtain ⟨hnew, inew⟩ := L.contourGraftGapBend_endpoint_transfer_of_parent S new_child parent
    new_parent new new_gap slot last false true new_out new_entry
  have no_other_old (flag : Bool) (t : Time) (h : EndAt flag t.1 t.2 = old_center) :
      t = first_time ∨ t = closing := (iold flag t h).2.symm
  have no_other_new (flag : Bool) (t : Time) (h : EndAt flag t.1 t.2 = new_center) :
      t = last_time ∨ t = closing := (inew flag t h).2.symm
  have ends (i : Fin (A.length + 1)) (flag : Bool) (t : Time) :
      EndAt flag t.1 t.2 = roof i ↔
        (flag = false ∧ t = ⟨⟨at_edge (A.previous old_child i), 0⟩, 1⟩) ∨
        (flag = true ∧ t = ⟨⟨at_edge (A.following new_child i),
          Fin.last (Stack (at_edge (A.following new_child i))).length⟩, 1⟩) :=
    L.contourGraftRoofWedge_endpoint_iff S
      (A.previous old_child i) (A.following new_child i) (A.visit i)
      (A.previous_returns old_child rfl i) (A.following_enters new_child rfl i)
      ((A.at_visit i).1.symm ▸ parent.property) flag t
  have end_at_zero (i : Fin A.length) :
      Fin.last (Stack (at_edge (A.child i))).length = 0 := by
    apply Fin.ext
    change (Stack (at_edge (A.child i))).length = 0
    rw [show Stack (at_edge (A.child i)) = [] from empty i]
    rfl
  have first_roof : EndAt false first_time.1 first_time.2 = roof 0 :=
    (ends 0 false first_time).mpr (Or.inl ⟨rfl, rfl⟩)
  have last_roof : EndAt true last_time.1 last_time.2 = roof (Fin.last A.length) := by
    apply (ends (Fin.last A.length) true last_time).mpr
    exact Or.inr ⟨rfl, by rw [A.following_last]⟩
  have left (i : Fin A.length) : EndAt true (times i).1 (times i).2 = roof i.castSucc := by
    apply (ends i.castSucc true (times i)).mpr
    exact Or.inr ⟨rfl, by rw [A.following_castSucc, end_at_zero]⟩
  have right (i : Fin A.length) : EndAt false (times i).1 (times i).2 = roof i.succ :=
    (ends i.succ false (times i)).mpr (Or.inl ⟨rfl, rfl⟩)
  have no_other_roof (i : Fin (A.length + 1)) (flag : Bool) (t : Time)
      (h : EndAt flag t.1 t.2 = roof i) :
      t = first_time ∨ t = last_time ∨ ∃ k, t = times k := by
    rcases (ends i flag t).mp h with ⟨_, prev⟩ | ⟨_, next⟩
    · revert prev
      refine Fin.cases ?_ (fun j => ?_) i
      · exact fun eq => Or.inl eq
      · exact fun eq => Or.inr (Or.inr ⟨j, eq⟩)
    · revert next
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro eq
        rw [A.following_last] at eq
        exact Or.inr (Or.inl eq)
      · intro eq
        rw [A.following_castSucc, end_at_zero] at eq
        exact Or.inr (Or.inr ⟨j, eq⟩)
  have roof_unique : Function.Injective roof := by
    intro i j same
    let copy (k : Fin (A.length + 1)) := (D).boundaryEndVertex Retain
      (S.contour.cycle.point (A.visit k))
    have value : Map ((D).vertexPoint Retain (copy i)) = Map ((D).vertexPoint Retain (copy j)) :=
      eq_of_heq (Sigma.mk.inj same).2
    have nonroot : (D).contourOriginalVertex Selection S.contour (A.visit i) ∉ (Fcut).parents.roots :=
      (A.at_visit i).1.symm ▸ parent.property
    have below := L.contourCutVertex_below S (copy i) nonroot
    have equal := L.fineMeshWholeMap_injective_at S.higher ((D).vertexPoint Retain (copy i)) ((D).vertexPoint Retain (copy j)) below value
    exact A.visit.injective ((D).boundaryCycle_vertices_injective Retain S.contour.cycle S.contour.closes
      ((D).vertexPoint_injective Retain equal))
  have old_member : old ∈ Stack above := show Valid ⟨above, some old, false, 0⟩ from
    old_out ▸ MetricGluing.bankStackEndpointAddress_valid Stack true closing.1 closing.2
  have new_member : new ∈ Stack above := show Valid ⟨above, some new, true, 0⟩ from
    new_out ▸ MetricGluing.bankStackEndpointAddress_valid Stack false closing.1 closing.2
  have old_tag : old_center.1 = some old :=
    congrArg Sigma.fst (MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap
      true closing above old old_member false 0 old_out)
  have new_tag : new_center.1 = some new :=
    congrArg Sigma.fst (MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap
      false closing above new new_member true 0 new_out)
  have different_events : old ≠ new := by
    have sorted : (Stack above).Pairwise (fun a b => b.val.val < a.val.val) :=
      ((D).contourEdgeGapStack_ordered Selection S.contour parent.val).reverse
    rw [adjacent] at sorted
    have ranked := (List.pairwise_cons.mp (List.pairwise_append.mp sorted).2.1).1 old
      List.mem_cons_self
    exact fun h => lt_irrefl _ (h ▸ ranked)
  have center_unique := MetricGluing.BankStackCyclicClass.runCenter_injective
    old_center new_center roof roof_unique (by
      intro eq
      exact different_events (Option.some.inj (old_tag.symm.trans
        ((congrArg Sigma.fst eq).trans new_tag)))) (by
      intro i eq
      have tag_eq : some old = (none : Option Event) := old_tag.symm.trans
        (congrArg (fun x : MetricGluing.Total Pieces => x.1) eq)
      cases tag_eq) (by
      intro i eq
      have tag_eq : some new = (none : Option Event) := new_tag.symm.trans
        (congrArg (fun x : MetricGluing.Total Pieces => x.1) eq)
      cases tag_eq)
  let H := MetricGluing.BankStackCyclicClass.ofRoofRun old_center new_center roof first_time
    last_time closing times hold.symm first_roof left right last_roof hnew.symm rfl rfl
    no_other_old no_other_new no_other_roof
  refine ⟨A, H, slot, new_out, old_out, rfl, ?_, ?_, rfl, rfl, empty, interval, center_unique⟩
  · have eq : Fin.last (A.length + 2) = (Fin.last (A.length + 1)).succ := (Fin.succ_last (A.length + 1)).symm
    rw [eq]
    change MetricGluing.BankStackCyclicClass.runCenter old_center new_center roof
      (Fin.last (A.length + 1)).succ = new_center
    exact MetricGluing.BankStackCyclicClass.runCenter_last old_center new_center roof
  · intro i
    change MetricGluing.BankStackCyclicClass.runCenter old_center new_center roof
      i.castSucc.succ = roof i
    exact MetricGluing.BankStackCyclicClass.runCenter_roof old_center new_center roof i

/-- At a cross-block adjacency, the original roof wedges and the two gap bends
are precisely the centers in the cyclic seam class. -/
theorem exists_contourGraftCrossBlockClass
    (parent old_child new_child : Edge)
    (old_parent : (Fcut).parents.parent old_child.val = parent.val)
    (new_parent : (Fcut).parents.parent new_child.val = parent.val)
    (different : old_child.val ≠ new_child.val) (old new : Event)
    (old_in : (Fcut).parents.Ancestor SourceOf[old] old_child.val)
    (new_in : (Fcut).parents.Ancestor SourceOf[new] new_child.val)
    (old_gap : OrientedBankGap BankAt[old] MovedAt[old])
    (new_gap : OrientedBankGap BankAt[new] MovedAt[new])
    (pre post : List Event)
    (adjacent : Stack FiniteBank[parent.val,parent.property] = pre ++ new :: old :: post) :
    let initial := finRotate (S.contour.length + 1) (Interval[old_child.val,old_child.property]).leave
    let final := (Interval[new_child.val,new_child.property]).enter
    let above := FiniteBank[parent.val,parent.property]
    ∃ (A : (D).ContourParentWedgeRun Selection S.contour (Fcut).boundary_roots S.starts
        parent.val initial final)
      (H : MetricGluing.BankStackCyclicClass Pieces Stack Base Gap (A.length + 2))
      (slot : Fin ((Stack above).length + 1)),
      Named false ⟨above, slot⟩ 0 = ⟨above, some new, true, 0⟩ ∧
      Named true ⟨above, slot⟩ 0 = ⟨above, some old, false, 0⟩ ∧
      H.center 0 = EndAt true ⟨above, slot⟩ 0 ∧
      H.center (Fin.last (A.length + 2)) = EndAt false ⟨above, slot⟩ 0 ∧
      ∀ i : Fin (A.length + 1), H.center i.castSucc.succ = RoofPoint[A.visit i] := by
  obtain ⟨A, H, slot, new_out, old_out, first, last, roof, _⟩ :=
    L.exists_contourGraftCrossBlockData S parent old_child new_child old_parent
      new_parent different old new old_in new_in old_gap new_gap pre post adjacent
  exact ⟨A, H, slot, new_out, old_out, first, last, roof⟩

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
