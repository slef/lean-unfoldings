module

public import Unfoldings.FewestNets.ThreeExitGraftTerminalAddresses
public import Unfoldings.FewestNets.ThreeExitGraftStrictFiber
public import Unfoldings.FewestNets.ThreeExitGraftMarkMetrics
public import Unfoldings.Metric.BankStackAdjacentGaps

/-! The exact seam classes at a terminal join have two equivalent parameter names. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel

open MetricGluing

universe u v

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

local instance graftJoinClassIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

local notation "restore" =>
  SpatialEnvelope.WholePartition.restoreCut L.whole.partition R.wholeCarrier
local notation "Path[" e "]" => PotentialCutForest.contourSourceSpatialRay Fcut S.contour S.starts e
local notation "Fold" => contourGraftPieceCollapse L S
local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Graft" => contourGraft L S
local notation "Banks" => MetricGluing.bankSeams Left Right

local notation "Phys" => contourPhysicalAddress L S
local notation "Exit" => TriangleComplex.ContourTerminalEdge D Selection
local notation "Child[" e "]" => Subtype.mk (Subtype.val e) (And.left (Subtype.property e))
local notation "TailPair[" e "]" => (Sigma.mk (Sum.inr e) 0 : Σ b : Attachment, Param b)
local notation "LastPair[" e "]" => (Sigma.mk (Sum.inl Child[e]) 1 : Σ b : Attachment, Param b)
local notation "TailSlot[" e "," i "]" => (Sigma.mk (Sum.inr e) i : BankStackSlot Stack)
local notation "LastSlot[" e "," i "]" => (Sigma.mk (Sum.inl Child[e]) i : BankStackSlot Stack)
local notation "Endpoint" => bankStackEndpoint Stack Pieces Base Gap
local notation "Address" => bankStackEndpointAddress (Parameter := Param) Stack
local notation "Length[" e "]" => TriangleComplex.positiveContourBankLength D Selection S.contour e

private theorem join_bool_injective {X : Type*} (mark : Bool → X) (apart : mark false ≠ mark true) :
    Function.Injective mark := by
  intro a b equal
  cases a <;> cases b
  · rfl
  · exact (apart equal).elim
  · exact (apart equal.symm).elim
  · rfl

/-- The tail join is strictly beyond the source of every gap passing through it. -/
theorem contourGraftGap_tail_zero_ne_start (event : Event) :
    let R := PotentialCutForest.contourSourceRay Fcut S.contour S.starts event
    R.tail 0 ≠ R.start := by
  let R := PotentialCutForest.contourSourceRay Fcut S.contour S.starts event
  change R.tail 0 ≠ R.start
  have vertices (i : Fin (Length[event] + 1)) : R.chain.vertex i.castSucc ≠ R.chain.vertex i.succ :=
    (sub_ne_zero.mp (contourGap_edge_ne_zero S event false i)).symm
  rw [PolygonalRay.tail_zero, ← show
    (Fin.last (Length[event])).succ = Fin.last (Length[event] + 1) from rfl,
    ← R.chain.point_one]
  exact R.point_ne_start (S.gaps event).first_outward vertices (Fin.last (Length[event]))
    1 (by norm_num)

private theorem join_gap_sides_ne (edge : Exit) (event : Event)
    (saved : event ∈ Stack (.inr edge)) :
    Gap (.inr edge) event saved false 0 ≠ Gap (.inr edge) event saved true 0 := by
  let model := Model[event]
  intro same
  have location :
      model.addressFrontier false (.inr 0) = model.addressFrontier true (.inr 0) :=
    Subtype.ext (congrArg PolygonalPoint.val same.symm)
  have side := model.side_eq_of_address_eq (S.gaps event) false true (.inr 0) (.inr 0)
    (contourGraftGap_tail_zero_ne_start S event) location
  cases side

private theorem join_mark_parameters (edge : Exit) :
    BankStackMarkParametersAt Stack Pieces Base Gap (.inr edge) 0
      (fun p => p = TailPair[edge] ∨ p = LastPair[edge]) := by
  constructor
  · intro side a flag t equal
    have same : Phys a t = Phys (.inr edge) 0 :=
      (L.contourPhysicalAddress_side S a flag t).symm.trans
        ((congrArg (fun x : L.whole.Cut => Cap.horizontal (restore x).val) equal).trans
          (L.contourPhysicalAddress_side S (.inr edge) side 0))
    have injective : Function.Injective (fun side => Base (.inr edge) side 0) :=
      join_bool_injective _ ((L.contourTerminalContinuation S.higher S.contour S.starts edge).disjoint
        false true (by decide) 0 0)
    rcases L.contourPhysicalAddress_eq_terminalJoin S edge a t same with finite | tail
    · have at_end : a = .inl Child[edge] := congrArg Sigma.fst finite
      subst a
      have time : t = 1 := eq_of_heq (Sigma.mk.inj finite).2
      subst t
      exact ⟨injective ((L.contourBaseMark_tail_zero S edge flag).trans equal), Or.inr rfl⟩
    · have at_tail : a = .inr edge := congrArg Sigma.fst tail
      subst a
      have time : t = 0 := eq_of_heq (Sigma.mk.inj tail).2
      subst t
      exact ⟨injective equal, Or.inl rfl⟩
  · intro event saved side a member flag t equal
    have spatial := (L.contourGraftPieceCollapse_gap_eq S a event member flag t).symm.trans
      ((congrArg (Fold (some event)) equal).trans
        (L.contourGraftPieceCollapse_gap_eq S (.inr edge) event saved side 0))
    have same : Phys a t = Phys (.inr edge) 0 :=
      (L.contourPhysicalAddress_side S a flag t).symm.trans
        ((congrArg Cap.horizontal spatial).trans (L.contourPhysicalAddress_side S (.inr edge) side 0))
    have injective : Function.Injective (fun flag => Gap (.inr edge) event saved flag 0) :=
      join_bool_injective _ (join_gap_sides_ne S edge event saved)
    rcases L.contourPhysicalAddress_eq_terminalJoin S edge a t same with finite | tail
    · have at_end : a = .inl Child[edge] := congrArg Sigma.fst finite
      subst a
      have time : t = 1 := eq_of_heq (Sigma.mk.inj finite).2
      subst t
      have join := PotentialCutForest.contourGapMark_tail_zero Fcut S.contour S.starts
        (fun e : Event => Model[e]) edge event saved flag
      exact ⟨injective (join.trans equal), Or.inr rfl⟩
    · have at_tail : a = .inr edge := congrArg Sigma.fst tail
      subst a
      have time : t = 0 := eq_of_heq (Sigma.mk.inj tail).2
      subst t
      exact ⟨injective equal, Or.inl rfl⟩

/-- The finite and tail slots of one original terminal edge use the same piece and side. -/
theorem contourGraft_terminalJoin_address_shift
    (edge : Exit) (i : Fin ((Stack (.inr edge)).length + 1)) (side : Bool) :
    let a := Address side TailSlot[edge,i] 0
    Address side LastSlot[edge,i] 1 = ⟨.inl Child[edge], a.2.1, a.2.2.1, 1⟩ := by
  let tail_slot := TailSlot[edge,i]
  let last_slot := LastSlot[edge,i]
  let P (a b : BankStackAddress («G» := Event) (Parameter := Param)) :=
    b = ⟨.inl Child[edge], a.2.1, a.2.2.1, 1⟩
  cases side
  · change P (bankStackLeftAddress (Parameter := Param) Stack tail_slot 0)
      (bankStackLeftAddress (Parameter := Param) Stack last_slot 1)
    unfold bankStackLeftAddress
    by_cases first : i.val = 0
    · rw [dite_eq_left (show tail_slot.2.val = 0 from first),
          dite_eq_left (show last_slot.2.val = 0 from first)]
    · rw [dite_eq_right (show tail_slot.2.val ≠ 0 from first),
          dite_eq_right (show last_slot.2.val ≠ 0 from first)]
      rfl
  · change P (bankStackRightAddress (Parameter := Param) Stack tail_slot 0)
      (bankStackRightAddress (Parameter := Param) Stack last_slot 1)
    unfold bankStackRightAddress
    by_cases before : i.val < (Stack (.inr edge)).length
    · rw [dite_eq_left (show tail_slot.2.val < (Stack tail_slot.1).length from before),
          dite_eq_left (show last_slot.2.val < (Stack last_slot.1).length from before)]
      rfl
    · rw [dite_eq_right (show ¬ tail_slot.2.val < (Stack tail_slot.1).length from before),
          dite_eq_right (show ¬ last_slot.2.val < (Stack last_slot.1).length from before)]

/-- Either endpoint of the actual terminal slot is also the endpoint of the same
consecutive finite slot. The roof tags and original gap tags are retained. -/
theorem contourGraft_terminalJoin_endpoint
    (edge : Exit) (i : Fin ((Stack (.inr edge)).length + 1)) (side : Bool) :
    Endpoint side LastSlot[edge,i] 1 = Endpoint side TailSlot[edge,i] 0 := by
  have base (side : Bool) := L.contourBaseMark_tail_zero S edge side
  have gap (event : Event) (member : event ∈ Stack (.inr edge)) (side : Bool) :=
    PotentialCutForest.contourGapMark_tail_zero Fcut S.contour S.starts
      (fun e : Event => Model[e]) edge event member side
  cases side
  · change bankStackLeft Pieces Stack Base Gap LastSlot[edge,i] 1 =
      bankStackLeft Pieces Stack Base Gap TailSlot[edge,i] 0
    unfold bankStackLeft
    split_ifs
    · exact congrArg (Sigma.mk none) (base false).symm
    · exact congrArg (Sigma.mk _) (gap _ (List.getElem_mem _) true).symm
  · change bankStackRight Pieces Stack Base Gap LastSlot[edge,i] 1 =
      bankStackRight Pieces Stack Base Gap TailSlot[edge,i] 0
    unfold bankStackRight
    by_cases before : i.val < (Stack (.inr edge)).length
    · rw [dite_eq_left (show (LastSlot[edge,i]).2.val < (Stack (LastSlot[edge,i]).1).length
            from before),
          dite_eq_left (show (TailSlot[edge,i]).2.val < (Stack (TailSlot[edge,i]).1).length
            from before)]
      exact congrArg (Sigma.mk _) (gap _ (List.getElem_mem _) false).symm
    · rw [dite_eq_right (show ¬ (LastSlot[edge,i]).2.val < (Stack (LastSlot[edge,i]).1).length
            from before),
          dite_eq_right (show ¬ (TailSlot[edge,i]).2.val < (Stack (TailSlot[edge,i]).1).length
            from before)]
      exact congrArg (Sigma.mk none) (base true).symm

/-- Equality with an original join mark recovers its endpoint side and its finite or
terminal slot address. -/
theorem contourGraft_terminalJoin_endpoint_eq
    (edge : Exit) (i : Fin ((Stack (.inr edge)).length + 1)) (side other_side : Bool)
    (other : BankStackSlot Stack) (s : Param other.1)
    (equal : Endpoint other_side other s = Endpoint side TailSlot[edge,i] 0) :
    other_side = side ∧
      ((⟨other, s⟩ : Σ slot : BankStackSlot Stack, Param slot.1) = ⟨TailSlot[edge,i], 0⟩ ∨
        (⟨other, s⟩ : Σ slot : BankStackSlot Stack, Param slot.1) = ⟨LastSlot[edge,i], 1⟩) := by
  let P (p : Σ b, Param b) := p = TailPair[edge] ∨ p = LastPair[edge]
  have covered : BankStackMarkParametersAt Stack Pieces Base Gap (.inr edge) 0 P :=
    L.join_mark_parameters S edge
  let b := Address other_side other s
  let a := Address side TailSlot[edge,i] 0
  obtain ⟨piece, flag, choice⟩ := bankStackEndpoint_tags_of_point_eq Stack Pieces Base Gap side
    other_side TailSlot[edge,i] other 0 s covered equal
  have assemble (p : Σ b, Param b) (same : (⟨b.1, b.2.2.2⟩ : Σ b, Param b) = p) :
      b = ⟨p.1, a.2.1, a.2.2.1, p.2⟩ := by
    change b.2.1 = a.2.1 at piece
    change b.2.2.1 = a.2.2.1 at flag
    calc
      b = ⟨b.1, a.2.1, a.2.2.1, b.2.2.2⟩ := by rw [← piece, ← flag]
      _ = _ := congrArg (fun q : Σ b, Param b =>
        (⟨q.1, a.2.1, a.2.2.1, q.2⟩ : BankStackAddress («G» := _) (Parameter := _))) same
  have nodup := contourGraft_stack_nodup S
  have key := bankStackEndpointAddress_parameter Stack other_side other s
  rcases choice with tail | last
  · have addresses : b = a := by
      have a_key := bankStackEndpointAddress_parameter (Parameter := Param) Stack side
        TailSlot[edge,i] (0 : ℝ≥0)
      change (⟨a.1, a.2.2.2⟩ : Σ b, Param b) = TailPair[edge] at a_key
      exact assemble ⟨a.1, a.2.2.2⟩ (key.trans (tail.trans a_key.symm))
    have eq := bankStackEndpointAddress_injective Stack nodup
      (a₁ := (other_side, ⟨other, s⟩)) (a₂ := (side, ⟨TailSlot[edge,i], 0⟩)) addresses
    exact ⟨congrArg Prod.fst eq, Or.inl (congrArg Prod.snd eq)⟩
  · have addresses : b = Address side LastSlot[edge,i] 1 :=
      (assemble LastPair[edge] (key.trans last)).trans
        (contourGraft_terminalJoin_address_shift S edge i side).symm
    have eq := bankStackEndpointAddress_injective Stack nodup
      (a₁ := (other_side, ⟨other, s⟩)) (a₂ := (side, ⟨LastSlot[edge,i], 1⟩)) addresses
    exact ⟨congrArg Prod.fst eq, Or.inr (congrArg Prod.snd eq)⟩

/-- The join aliases introduce exactly the same two copies as one genuine slot. -/
theorem contourGraft_terminalJoin_eqvGen_pair (edge : Exit)
    (i : Fin ((Stack (.inr edge)).length + 1)) (x : MetricGluing.Total Pieces) :
    Relation.EqvGen Banks (Left TailSlot[edge,i] 0) x ↔
      x = Left TailSlot[edge,i] 0 ∨ x = Right TailSlot[edge,i] 0 := by
  let first : Σ slot : BankStackSlot Stack, Param slot.1 := ⟨TailSlot[edge,i], 0⟩
  let second : Σ slot : BankStackSlot Stack, Param slot.1 := ⟨LastSlot[edge,i], 1⟩
  exact bankStack_eqvGen_pair_of_two_slot_times Stack Pieces Base Gap first second
    (fun side => (L.contourGraft_terminalJoin_endpoint S edge i side).symm)
    (fun side other p => L.contourGraft_terminalJoin_endpoint_eq S edge i side other p.1 p.2) x

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
