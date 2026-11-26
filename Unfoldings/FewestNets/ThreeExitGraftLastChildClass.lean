module

public import Unfoldings.FewestNets.ThreeExitGraftCrossBlockClasses
public import Unfoldings.FewestNets.ThreeExitGraftRoofRun
public import Unfoldings.Complex.ContourExtremeChildWedgeRun
public import Unfoldings.Metric.BankStackSingleBendCycle


/-! The cyclic class from the last child to the parent bank. -/

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

local instance graftLastChildClassIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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
local notation "RoofSite" => Edge × Bool × Bool
local notation "SiteTime" => contourGraftRoofSiteTime S
local notation "AtSite[" a "]" => Germ (Prod.fst a) (Prod.fst (Prod.snd a))
  (Prod.snd (Prod.snd a))

set_option maxHeartbeats 800000 in
-- The exact left and right incidents use the same dependent finite bank parameter.
private theorem final_roof_wedge_endpoint_iff (child parent : Edge)
    (j : Fin (S.contour.length + 1))
    (after : finRotate (S.contour.length + 1) (Interval[child.val,child.property]).leave = j)
    (at_exit : (Interval[parent.val,parent.property]).leave = j)
    (nonroot : (D).contourOriginalVertex Selection S.contour j ∉ (Fcut).parents.roots)
    (flag : Bool) (s : Time) :
    let a := FiniteBank[child.val,child.property]
    let b := FiniteBank[parent.val,parent.property]
    EndAt flag s.1 s.2 = RoofPoint[j] ↔
      flag = false ∧ (s = ⟨⟨a, 0⟩, 1⟩ ∨ s = ⟨⟨b, 0⟩, 0⟩) := by
  let a := FiniteBank[child.val,child.property]
  let b := FiniteBank[parent.val,parent.property]
  let start : Time := ⟨⟨a, 0⟩, 1⟩
  let finish : Time := ⟨⟨b, 0⟩, 0⟩
  let w := (D).boundaryEndVertex Retain (S.contour.cycle.point j)
  let x := Map ((D).vertexPoint Retain w)
  have first : Germ child false true = (D).boundaryMate Retain (S.contour.cycle.point j) := by
    rw [← after]
    have next := S.contour.next_cyclic (D) (Interval[child.val,child.property]).leave
    exact ((D).boundaryMate_involutive Retain _).symm.trans
      (congrArg ((D).boundaryMate Retain) next)
  have last : Germ parent false false = S.contour.cycle.point j := by
    rw [← at_exit]
    rfl
  have at_zero : finiteSlotParameterize false 0 = 0 := rfl
  have at_one : finiteSlotParameterize true 0 = 1 := unitInterval.symm_zero
  have names (bank : Attachment) (side : Bool) (t : Param bank) :
      Base bank side t = x ↔
        ((⟨bank, t⟩ : Σ b : Attachment, Param b) = ⟨a, 1⟩ ∧ side = false) ∨
        ((⟨bank, t⟩ : Σ b : Attachment, Param b) = ⟨b, 0⟩ ∧ side = false) := by
    simpa only [at_zero, at_one] using
      L.contourRoofVertex_baseMark_iff_of_germs S child parent false false
        true false j first last nonroot bank side t
  have name_start : Named false start.1 start.2 = ⟨a, none, false, 1⟩ := by
    simp [start, MetricGluing.bankStackEndpointAddress, MetricGluing.bankStackLeftAddress]
  have name_finish : Named false finish.1 finish.2 = ⟨b, none, false, 0⟩ := by
    simp [finish, MetricGluing.bankStackEndpointAddress, MetricGluing.bankStackLeftAddress]
  have named (u : Time) (bank : Attachment) (t : Param bank)
      (value : Named false u.1 u.2 = ⟨bank, none, false, t⟩)
      (position : Base bank false t = x) : EndAt false u.1 u.2 = RoofPoint[j] :=
    (MetricGluing.bankStackEndpoint_eq_of_base_address Stack Pieces Base Gap false u
      bank false t value).trans (congrArg (Sigma.mk none) position)
  constructor
  · intro h
    have nodup := contourGraft_stack_nodup S
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
        · exact Or.inl (congrArg (fun z : Σ b : Attachment, Param b =>
            (⟨z.1, none, false, z.2⟩ : Addr)) times)
        · exact Or.inr (congrArg (fun z : Σ b : Attachment, Param b =>
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
theorem exists_contourGraftLastChildClass
    (parent child : Edge) (parent_eq : (Fcut).parents.parent child.val = parent.val)
    (event : Event) (in_child : (Fcut).parents.Ancestor SourceOf[event] child.val)
    (g : OrientedBankGap BankAt[event] MovedAt[event])
    (older : List Event) (head : Stack FiniteBank[parent.val,parent.property] = event :: older) :
    let first := finRotate (S.contour.length + 1) (Interval[child.val,child.property]).leave
    let last := (Interval[parent.val,parent.property]).leave
    let a := FiniteBank[child.val,child.property]
    let b := FiniteBank[parent.val,parent.property]
    ∃ (A : (D).ContourParentWedgeRun Selection S.contour (Fcut).boundary_roots S.starts
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
      ((D).contourEdgeGapStack_ordered Selection S.contour parent.val).reverse
    rw [head] at sorted member
    rcases List.mem_cons.mp member with rfl | in_tail
    · exact le_rfl
    · exact ((List.pairwise_cons.mp sorted).1 e in_tail).le
  have at_child : event ∈ Stack a :=
    ((D).mem_contourSavedGapStack Selection S.contour child.val event).mpr in_child
  have latest_child (e : Event) (member : e ∈ Stack a) : e.val.val ≤ event.val.val :=
    newest e (((D).mem_contourSavedGapStack Selection S.contour parent.val e).mpr
      ((((D).mem_contourSavedGapStack Selection S.contour child.val e).mp member).trans (Fcut).parents
        (parent_eq ▸ (Fcut).parents.ancestor_parent child.val)))
  have child_shape : ∃ rest, Stack a = event :: rest := by
    have sorted : (Stack a).Pairwise (fun a b => b.val.val < a.val.val) :=
      ((D).contourEdgeGapStack_ordered Selection S.contour child.val).reverse
    cases h : Stack a with
    | nil => rw [h] at at_child; cases at_child
    | cons first rest =>
      rw [h] at sorted at_child
      rcases List.mem_cons.mp at_child with same | after
      · exact ⟨rest, congrArg (fun e => e :: rest) same.symm⟩
      · exact (not_lt_of_ge (latest_child first (h.symm ▸ List.mem_cons_self)))
          ((List.pairwise_cons.mp sorted).1 event after) |>.elim
  obtain ⟨rest, child_head⟩ := child_shape
  obtain ⟨A, empty⟩ := (D).exists_contourLastChildWedgeRun Selection S.contour (Fcut).boundary_roots
    S.starts parent child parent_eq event in_child newest
  let roof (i : Fin (A.length + 1)) := RoofPoint[A.visit i]
  let bank (e : Edge) := FiniteBank[e.val,e.property]
  let time (i : Fin A.length) : Time := ⟨⟨bank (A.child i), 0⟩, 1⟩
  have closing := MetricGluing.bankStack_first_gap_addresses (Parameter := Param)
    Stack b 0 event older head
  have opening := MetricGluing.bankStack_first_gap_addresses (Parameter := Param)
    Stack a 1 event rest child_head
  have bend_transfer : EndAt true closure.1 closure.2 = EndAt true entrance.1 entrance.2 ∧
      ∀ (flag : Bool) (s : Time), EndAt flag s.1 s.2 = bend →
        flag = true ∧ (s = closure ∨ s = entrance) := by
    obtain ⟨w, nonroot⟩ := parent
    change (Fcut).parents.parent child.val = w at parent_eq
    subst w
    exact L.contourGraftGapBend_endpoint_transfer S
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
    have nonroot : (D).contourOriginalVertex Selection S.contour (A.visit i.castSucc) ∉
        (Fcut).parents.roots := (A.at_visit i.castSucc).1.symm ▸ parent.property
    have h := L.contourGraftRoofWedge_endpoint_iff S
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
    final_roof_wedge_endpoint_iff L S (A.previous child (Fin.last A.length)) parent
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
      (S.contour.cycle.point (A.visit k))
    have value : Map ((D).vertexPoint Retain (copy i)) = Map ((D).vertexPoint Retain (copy j)) :=
      eq_of_heq (Sigma.mk.inj same).2
    have nonroot : (D).contourOriginalVertex Selection S.contour (A.visit i) ∉ (Fcut).parents.roots :=
      (A.at_visit i).1.symm ▸ parent.property
    have below := L.contourCutVertex_below S (copy i) nonroot
    have equal := L.fineMeshWholeMap_injective_at S.higher ((D).vertexPoint Retain (copy i)) ((D).vertexPoint Retain (copy j)) below value
    exact A.visit.injective ((D).boundaryCycle_vertices_injective Retain S.contour.cycle S.contour.closes
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

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
