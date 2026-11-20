module

public import Unfoldings.Complex.ContourChildBlockWedgeRun
public import Unfoldings.Metric.BankStackCyclicClass
public import Unfoldings.Roof.CompatibleContourSourceOnlyChildPairClasses
public import Unfoldings.Roof.CompatibleContourSourceOnlyWedgeEndpoints

/-! The actual cyclic seam class between different child gap blocks. -/

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

local instance sourceOnlyCrossBlockIndexFintype : Fintype (T).Index :=
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
  (models : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    BankGapModel
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance sourceOnlyCrossBlockWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
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

private theorem source_only_bend_transfer_at_parent
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
  exact compatibleContourSourceOnlyGapBend_endpoint_transfer K compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models child.val child.property
    nonroot e g i j side flag outgoing incoming

/-- At a cross-block adjacency, two gap bends and the intervening original roof wedges
form precisely one cyclic seam class, in the original contour order. -/
theorem exists_compatibleContourSourceOnlyCrossBlockData
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
    let initial := finRotate (contour.length + 1) (Interval[old_child.val,old_child.property]).leave
    let final := (Interval[new_child.val,new_child.property]).enter
    let above := FiniteBank[parent.val,parent.property]
    ∃ (A : (D).ContourParentWedgeRun Selection contour (Fcut).boundary_roots starts
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
      (∀ j : Fin (contour.length + 1), (∃ i, A.visit i = j) ↔
        (D).contourOriginalVertex Selection contour j = parent.val ∧
          j ≠ (Interval[parent.val,parent.property]).leave ∧
            old.val.val ≤ j.val ∧ j.val < new.val.val) ∧
      Function.Injective H.center := by
  obtain ⟨A, ⟨older, old_shape⟩, ⟨newer, new_shape⟩, empty, interval⟩ :=
    (D).exists_contourChildBlockWedgeRun Selection contour (Fcut).boundary_roots starts
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
    (Parameter := ParamAt) Stack above 0 adjacent
  let closing : Time := ⟨⟨above, slot⟩, 0⟩
  let old_center := EndAt true closing.1 closing.2
  let new_center := EndAt false closing.1 closing.2
  have old_entry := (MetricGluing.bankStack_first_gap_addresses (Parameter := ParamAt)
    Stack a 1 old older old_shape').2
  have new_entry := (MetricGluing.bankStack_last_gap_addresses (Parameter := ParamAt)
    Stack b 1 new newer new_shape').1
  obtain ⟨hold, iold⟩ := source_only_bend_transfer_at_parent K compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models old_child parent
    old_parent old old_gap slot 0 true false old_out old_entry
  obtain ⟨hnew, inew⟩ := source_only_bend_transfer_at_parent K compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models new_child parent
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
    K.compatibleContourSourceOnlyRoofWedge_endpoint_iff compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W models
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
      (contour.cycle.point (A.visit k))
    have value : Map ((D).vertexPoint Retain (copy i)) = Map ((D).vertexPoint Retain (copy j)) :=
      eq_of_heq (Sigma.mk.inj same).2
    have nonroot : (D).contourOriginalVertex Selection contour (A.visit i) ∉ (Fcut).parents.roots :=
      (A.at_visit i).1.symm ▸ parent.property
    have below := K.compatibleContourRoofVertex_height_lt_of_nonroot compact nonempty R no_boundary
      level higher M positive inner_disk beta acute (copy i) nonroot
    have equal := K.compatibleMeshWholeMap_injective_at compact nonempty R no_boundary level higher
      M positive inner_disk beta acute W ((D).vertexPoint Retain (copy i)) below
      ((D).vertexPoint Retain (copy j)) value
    exact A.visit.injective ((D).boundaryCycle_vertices_injective Retain contour.cycle contour.closes
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
      ((D).contourEdgeGapStack_ordered Selection contour parent.val).reverse
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
    simp only [H, MetricGluing.BankStackCyclicClass.ofRoofRun,
      MetricGluing.BankStackCyclicClass.runCenter_roof, roof]

/-- At a cross-block adjacency, the original roof wedges and the two gap bends
are precisely the centers in the cyclic seam class. -/
theorem exists_compatibleContourSourceOnlyCrossBlockClass
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
    let initial := finRotate (contour.length + 1) (Interval[old_child.val,old_child.property]).leave
    let final := (Interval[new_child.val,new_child.property]).enter
    let above := FiniteBank[parent.val,parent.property]
    ∃ (A : (D).ContourParentWedgeRun Selection contour (Fcut).boundary_roots starts
        parent.val initial final)
      (H : MetricGluing.BankStackCyclicClass Pieces Stack Base Gap (A.length + 2))
      (slot : Fin ((Stack above).length + 1)),
      Named false ⟨above, slot⟩ 0 = ⟨above, some new, true, 0⟩ ∧
      Named true ⟨above, slot⟩ 0 = ⟨above, some old, false, 0⟩ ∧
      H.center 0 = EndAt true ⟨above, slot⟩ 0 ∧
      H.center (Fin.last (A.length + 2)) = EndAt false ⟨above, slot⟩ 0 ∧
      ∀ i : Fin (A.length + 1), H.center i.castSucc.succ = RoofPoint[A.visit i] := by
  obtain ⟨A, H, slot, new_out, old_out, first, last, roof, _⟩ :=
    K.exists_compatibleContourSourceOnlyCrossBlockData compact nonempty R no_boundary level higher
      M positive inner_disk beta acute contour starts W models parent old_child new_child old_parent
      new_parent different old new old_in new_in old_gap new_gap pre post adjacent
  exact ⟨A, H, slot, new_out, old_out, first, last, roof⟩

end Unfoldings.ConvexRoof
