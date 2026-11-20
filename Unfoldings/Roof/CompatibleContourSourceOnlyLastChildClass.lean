module

public import Unfoldings.Roof.CompatibleContourSourceOnlyCrossBlockClasses
public import Unfoldings.Roof.CompatibleContourFiniteRoofEndpoints
public import Unfoldings.Complex.ContourExtremeChildWedgeRun
public import Unfoldings.Metric.BankStackSingleBendCycle

/-! The final child gap bend closes its cycle through the outgoing roof bank. -/

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

local instance sourceOnlyLastChildIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlyLastChildWholeFintype : Fintype W.Index := W.finiteIndex

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


local notation "Germ" => K.compatibleContourFiniteRoofGerm compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts

set_option maxHeartbeats 800000 in
-- The exact left and right incidents use the same dependent finite bank parameter.
private theorem final_roof_wedge_endpoint_iff (child parent : Edge)
    (j : Fin (contour.length + 1))
    (after : finRotate (contour.length + 1) (Interval[child.val,child.property]).leave = j)
    (at_exit : (Interval[parent.val,parent.property]).leave = j)
    (nonroot : (D).contourOriginalVertex Selection contour j ∉ (Fcut).parents.roots)
    (flag : Bool) (s : Time) :
    let a := FiniteBank[child.val,child.property]
    let b := FiniteBank[parent.val,parent.property]
    EndAt flag s.1 s.2 = RoofPoint[j] ↔
      flag = false ∧ (s = ⟨⟨a, 0⟩, 1⟩ ∨ s = ⟨⟨b, 0⟩, 0⟩) := by
  let a := FiniteBank[child.val,child.property]
  let b := FiniteBank[parent.val,parent.property]
  let start : Time := ⟨⟨a, 0⟩, 1⟩
  let finish : Time := ⟨⟨b, 0⟩, 0⟩
  let w := (D).boundaryEndVertex Retain (contour.cycle.point j)
  let x := Map ((D).vertexPoint Retain w)
  have first : Germ child false true = (D).boundaryMate Retain (contour.cycle.point j) := by
    rw [← after]
    have next := contour.next_cyclic (D) (Interval[child.val,child.property]).leave
    exact ((D).boundaryMate_involutive Retain _).symm.trans
      (congrArg ((D).boundaryMate Retain) next)
  have last : Germ parent false false = contour.cycle.point j := by
    rw [← at_exit]
    rfl
  have at_zero : finiteSlotParameterize false 0 = 0 := rfl
  have at_one : finiteSlotParameterize true 0 = 1 := unitInterval.symm_zero
  have names (bank : Attachment) (side : Bool) (t : ParamAt bank) :
      Base bank side t = x ↔
        ((⟨bank, t⟩ : Σ b : Attachment, ParamAt b) = ⟨a, 1⟩ ∧ side = false) ∨
        ((⟨bank, t⟩ : Σ b : Attachment, ParamAt b) = ⟨b, 0⟩ ∧ side = false) := by
    simpa only [at_zero, at_one] using
      K.compatibleContourSourceOnlyRoofVertex_baseMark_iff_of_germs compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts W child parent false false
        true false j first last nonroot bank side t
  have name_start : Named false start.1 start.2 = ⟨a, none, false, 1⟩ := by
    simp [start, MetricGluing.bankStackEndpointAddress, MetricGluing.bankStackLeftAddress]
  have name_finish : Named false finish.1 finish.2 = ⟨b, none, false, 0⟩ := by
    simp [finish, MetricGluing.bankStackEndpointAddress, MetricGluing.bankStackLeftAddress]
  have named (u : Time) (bank : Attachment) (t : ParamAt bank)
      (value : Named false u.1 u.2 = ⟨bank, none, false, t⟩)
      (position : Base bank false t = x) : EndAt false u.1 u.2 = RoofPoint[j] :=
    (MetricGluing.bankStackEndpoint_eq_of_base_address Stack Pieces Base Gap false u
      bank false t value).trans (congrArg (Sigma.mk none) position)
  constructor
  · intro h
    have nodup := K.compatibleContourBankStack_nodup compact nonempty R no_boundary level higher
      M positive inner_disk beta acute contour
    let addr := Named flag s.1 s.2
    let valid := MetricGluing.bankStackEndpointAddress_valid Stack flag s.1 s.2
    have at_mark : Mark addr valid = ⟨none, x⟩ :=
      (MetricGluing.bankStackAddressPoint_endpoint Stack Pieces Base Gap flag s.1 s.2).trans h
    have recover (addr : Addr) (valid : Valid addr) (h : Mark addr valid = ⟨none, x⟩) :
        addr = ⟨a, none, false, 1⟩ ∨ addr = ⟨b, none, false, 0⟩ := by
      obtain ⟨bank, part, side, t⟩ := addr
      cases part with
      | some e => cases congrArg Sigma.fst h
      | none =>
        have mark : Base bank side t = x := eq_of_heq (Sigma.mk.inj h).2
        rcases (names bank side t).mp mark with ⟨times, rfl⟩ | ⟨times, rfl⟩
        · exact Or.inl (congrArg (fun z : Σ b : Attachment, ParamAt b =>
            (⟨z.1, none, false, z.2⟩ : Addr)) times)
        · exact Or.inr (congrArg (fun z : Σ b : Attachment, ParamAt b =>
            (⟨z.1, none, false, z.2⟩ : Addr)) times)
    rcases recover addr valid at_mark with a | b
    · have eq : (flag, s) = (false, start) :=
        MetricGluing.bankStackEndpointAddress_injective Stack nodup (a.trans name_start.symm)
      exact ⟨congrArg Prod.fst eq, Or.inl (congrArg Prod.snd eq)⟩
    · have eq : (flag, s) = (false, finish) :=
        MetricGluing.bankStackEndpointAddress_injective Stack nodup (b.trans name_finish.symm)
      exact ⟨congrArg Prod.fst eq, Or.inr (congrArg Prod.snd eq)⟩
  · rintro ⟨rfl, rfl | rfl⟩
    · exact named start a 1 name_start ((names a false 1).mpr (Or.inl ⟨rfl, rfl⟩))
    · exact named finish b 0 name_finish ((names b false 0).mpr (Or.inr ⟨rfl, rfl⟩))


set_option maxHeartbeats 1600000 in
-- Both stack heads and all exact incidents are related at their original dependent times.
/-- The newest gap bend and the remaining roof wedges give the entire seam class at
the exit side of a nonroot's outgoing bank. -/
theorem exists_compatibleContourSourceOnlyLastChildClass
    (parent child : Edge) (parent_eq : (Fcut).parents.parent child.val = parent.val)
    (event : Event) (in_child : (Fcut).parents.Ancestor SourceOf[event] child.val)
    (g : OrientedBankGap BankAt[event] MovedAt[event])
    (older : List Event) (head : Stack FiniteBank[parent.val,parent.property] = event :: older) :
    let first := finRotate (contour.length + 1) (Interval[child.val,child.property]).leave
    let last := (Interval[parent.val,parent.property]).leave
    let a := FiniteBank[child.val,child.property]
    let b := FiniteBank[parent.val,parent.property]
    ∃ (A : (D).ContourParentWedgeRun Selection contour (Fcut).boundary_roots starts
      parent.val first last)
      (H : MetricGluing.BankStackCyclicClass Pieces Stack Base Gap (A.length + 1)),
      H.center 0 = EndAt true ⟨b, 0⟩ 0 ∧
      (∀ i : Fin (A.length + 1), H.center i.succ = RoofPoint[A.visit i]) ∧
      H.time = MetricGluing.BankStackCyclicClass.singleTime
        (⟨⟨a, 0⟩, 1⟩ : Time) ⟨⟨b, 0⟩, 0⟩
        (fun i => ⟨⟨FiniteBank[(A.child i).val,(A.child i).property], 0⟩, 1⟩) ∧
      H.side = MetricGluing.BankStackCyclicClass.singleSide ∧
      (∀ i, Stack FiniteBank[(A.child i).val,(A.child i).property] = []) ∧
      (∃ before, Stack a = event :: before) ∧ Function.Injective H.center := by
  let a := FiniteBank[child.val,child.property]
  let b := FiniteBank[parent.val,parent.property]
  let entrance : Time := ⟨⟨a, 0⟩, 1⟩
  let closure : Time := ⟨⟨b, 0⟩, 0⟩
  let bend := EndAt true closure.1 closure.2
  have newest (e : Event) (member : e ∈ Stack b) : e.val.val ≤ event.val.val := by
    have sorted : (Stack b).Pairwise (fun a b => b.val.val < a.val.val) :=
      ((D).contourEdgeGapStack_ordered Selection contour parent.val).reverse
    rw [head] at sorted member
    rcases List.mem_cons.mp member with rfl | in_tail
    · exact le_rfl
    · exact ((List.pairwise_cons.mp sorted).1 e in_tail).le
  have at_child : event ∈ Stack a :=
    ((D).mem_contourSavedGapStack Selection contour child.val event).mpr in_child
  have latest_child (e : Event) (member : e ∈ Stack a) : e.val.val ≤ event.val.val :=
    newest e (((D).mem_contourSavedGapStack Selection contour parent.val e).mpr
      ((((D).mem_contourSavedGapStack Selection contour child.val e).mp member).trans (Fcut).parents
        (parent_eq ▸ (Fcut).parents.ancestor_parent child.val)))
  have child_shape : ∃ rest, Stack a = event :: rest := by
    have sorted : (Stack a).Pairwise (fun a b => b.val.val < a.val.val) :=
      ((D).contourEdgeGapStack_ordered Selection contour child.val).reverse
    cases h : Stack a with
    | nil => rw [h] at at_child; cases at_child
    | cons first rest =>
      rw [h] at sorted at_child
      rcases List.mem_cons.mp at_child with same | after
      · exact ⟨rest, congrArg (fun e => e :: rest) same.symm⟩
      · exact (not_lt_of_ge (latest_child first (h.symm ▸ List.mem_cons_self)))
          ((List.pairwise_cons.mp sorted).1 event after) |>.elim
  obtain ⟨rest, child_head⟩ := child_shape
  obtain ⟨A, empty⟩ := (D).exists_contourLastChildWedgeRun Selection contour (Fcut).boundary_roots
    starts parent child parent_eq event in_child newest
  let roof (i : Fin (A.length + 1)) := RoofPoint[A.visit i]
  let bank (e : Edge) := FiniteBank[e.val,e.property]
  let time (i : Fin A.length) : Time := ⟨⟨bank (A.child i), 0⟩, 1⟩
  have closing := MetricGluing.bankStack_first_gap_addresses (Parameter := ParamAt)
    Stack b 0 event older head
  have opening := MetricGluing.bankStack_first_gap_addresses (Parameter := ParamAt)
    Stack a 1 event rest child_head
  have bend_transfer : EndAt true closure.1 closure.2 = EndAt true entrance.1 entrance.2 ∧
      ∀ (flag : Bool) (s : Time), EndAt flag s.1 s.2 = bend →
        flag = true ∧ (s = closure ∨ s = entrance) := by
    obtain ⟨w, nonroot⟩ := parent
    change (Fcut).parents.parent child.val = w at parent_eq
    subst w
    exact K.compatibleContourSourceOnlyGapBend_endpoint_transfer compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W models
      child.val child.property nonroot event g 0 0 true false closing.2 opening.2
  have empty_last (i : Fin A.length) :
      Fin.last (Stack FiniteBank[(A.child i).val,(A.child i).property]).length = 0 := by
    apply Fin.ext
    change (Stack (bank (A.child i))).length = 0
    rw [show Stack (bank (A.child i)) = [] from empty i]
    rfl
  have interior (i : Fin A.length) (flag : Bool) (s : Time) :
      EndAt flag s.1 s.2 = roof i.castSucc ↔
        (flag = false ∧ s = ⟨⟨bank (A.previous child i.castSucc), 0⟩, 1⟩) ∨
        (flag = true ∧ s = time i) := by
    have nonroot : (D).contourOriginalVertex Selection contour (A.visit i.castSucc) ∉
        (Fcut).parents.roots := (A.at_visit i.castSucc).1.symm ▸ parent.property
    have h := K.compatibleContourSourceOnlyRoofWedge_endpoint_iff compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W models
      (A.previous child i.castSucc) (A.child i) (A.visit i.castSucc)
      (A.previous_returns child rfl i.castSucc) (A.enters i) nonroot flag s
    let e := bank (A.child i)
    let f (k : Fin ((Stack e).length + 1)) : Time := ⟨⟨e, k⟩, 1⟩
    have at_time : f (Fin.last (Stack e).length) = time i :=
      congrArg f (empty_last i)
    change EndAt flag s.1 s.2 = roof i.castSucc ↔
      (flag = false ∧ s = ⟨⟨bank (A.previous child i.castSucc), 0⟩, 1⟩) ∨
      (flag = true ∧ s = f (Fin.last (Stack e).length)) at h
    rw [at_time] at h
    exact h
  have final (flag : Bool) (s : Time) : EndAt flag s.1 s.2 = roof (Fin.last A.length) ↔
      flag = false ∧ (s = ⟨⟨bank (A.previous child (Fin.last A.length)), 0⟩, 1⟩ ∨
        s = closure) :=
    final_roof_wedge_endpoint_iff K compact nonempty R no_boundary level higher M positive inner_disk
      beta acute contour starts W models (A.previous child (Fin.last A.length)) parent
      (A.visit (Fin.last A.length)) (A.previous_returns child rfl _) A.at_last.symm
      ((A.at_visit (Fin.last A.length)).1.symm ▸ parent.property) flag s
  have left (i : Fin (A.length + 1)) (flag : Bool) (s : Time)
      (h : flag = false ∧ s = ⟨⟨bank (A.previous child i), 0⟩, 1⟩) :
      EndAt flag s.1 s.2 = roof i := by
    revert h
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact fun h => (final flag s).mpr ⟨h.1, Or.inl h.2⟩
    · exact fun h => (interior j flag s).mpr (Or.inl h)
  have roof_incident (i : Fin (A.length + 1)) (flag : Bool) (s : Time)
      (h : EndAt flag s.1 s.2 = roof i) : s = entrance ∨ s = closure ∨ ∃ k, s = time k := by
    have previous (j : Fin (A.length + 1)) (eq : s = ⟨⟨bank (A.previous child j), 0⟩, 1⟩) :
        s = entrance ∨ s = closure ∨ ∃ k, s = time k := by
      revert eq
      refine Fin.cases ?_ (fun k => ?_) j
      · exact Or.inl
      · exact fun eq => Or.inr (Or.inr ⟨k, eq⟩)
    revert h
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro h
      rcases ((final flag s).mp h).2 with p | c
      · exact previous _ p
      · exact Or.inr (Or.inl c)
    · intro h
      rcases (interior j flag s).mp h with ⟨_, p⟩ | ⟨_, t⟩
      · exact previous _ p
      · exact Or.inr (Or.inr ⟨j, t⟩)
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
  have bend_tag : bend.1 = some event := by
    have member : event ∈ Stack b := head.symm ▸ List.mem_cons_self
    exact congrArg Sigma.fst (MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap
      true closure b event member false 0 closing.2)
  have different (i : Fin (A.length + 1)) : bend ≠ roof i := by
    intro h
    have impossible : some event = (none : Option Event) := bend_tag.symm.trans (congrArg Sigma.fst h)
    cases impossible
  let H := MetricGluing.BankStackCyclicClass.ofSingleBendRun bend roof entrance closure time
    bend_transfer.1.symm (left 0 false entrance ⟨rfl, rfl⟩)
    (fun i => (interior i true (time i)).mpr (Or.inr ⟨rfl, rfl⟩))
    (fun i => left i.succ false (time i) ⟨rfl, rfl⟩)
    ((final false closure).mpr ⟨rfl, Or.inr rfl⟩) rfl
    (fun flag s h => ((bend_transfer.2 flag s h).2).elim Or.inr Or.inl) roof_incident
  exact ⟨A, H, rfl, fun _ => rfl, rfl, rfl, empty, ⟨rest, child_head⟩,
    MetricGluing.BankStackCyclicClass.singleCenter_injective bend roof roof_unique different⟩

end Unfoldings.ConvexRoof
