module

public import Unfoldings.FewestNets.ThreeExitGraftPhysicalAddresses
public import Unfoldings.Metric.BankStackArcFiber
public import Unfoldings.Metric.BankStackAddressPredicate
public import Unfoldings.Geometry.BankGapAddressUniqueness

/-! Over a strict finite or continued cut address, the whole collapse fiber is a chain of arcs. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel

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

local instance graftStrictFiberIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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
local notation "Addr[" a "," e "," saved "," t "]" =>
  PotentialCutForest.contourGapAddress Fcut S.contour a e saved t
local notation "Length[" e "]" => TriangleComplex.positiveContourBankLength D Selection S.contour e
local notation "Ray[" e "]" => PotentialCutForest.contourSourceRay Fcut S.contour S.starts e
local notation "Point" => MetricGluing.point Pieces Banks

/-- A parameter strictly inside a finite edge or strictly past a terminal join. -/
def strictContourParameter : (a : Attachment) → Param a → Prop
  | .inl _, t => 0 < t ∧ t < 1
  | .inr _, t => 0 < t

local notation "Strict" => strictContourParameter S

private theorem strictContourParameter_unique (b : Attachment) (t : Param b)
    (strict : Strict b t) (a : Attachment) (s : Param a) (pos : Phys a s = Phys b t) :
    (⟨a, s⟩ : Σ a : Attachment, Param a) = ⟨b, t⟩ := by
  cases b with
  | inl e => exact L.contourPhysicalAddress_eq_finite S e t strict a s pos
  | inr e => exact L.contourPhysicalAddress_eq_positiveTail S e t strict a s pos

private theorem strictContourParameter_roof_sides_ne (a : Attachment) (t : Param a)
    (strict : Strict a t) : Base a false t ≠ Base a true t := by
  cases a with
  | inl e =>
    exact L.contourParentMark_ne_of_inside S.higher S.contour S.starts e.val e.property t strict
      (L.contourPhysicalAddress_finite_lt S e t strict)
  | inr e =>
    exact (L.contourTerminalContinuation S.higher S.contour S.starts e).disjoint
      false true (by decide) t t

private theorem contourGap_strict_away (a : Attachment) (t : Param a)
    (strict : Strict a t) (e : Event) (saved : e ∈ Stack a) :
    Ray[e].addressPoint Addr[a,e,saved,t] ≠ Ray[e].start := by
  let bank := PotentialCutForest.contourSourceBankChain Fcut S.contour S.starts e
  have genuine (i : Fin (Length[e] + 1)) : Ray[e].chain.edge i ≠ 0 :=
    (D).boundaryChainRoll_edge_ne_zero bank i
  have vertices (i : Fin (Length[e] + 1)) : Ray[e].chain.vertex i.castSucc ≠ Ray[e].chain.vertex i.succ :=
    (sub_ne_zero.mp (genuine i)).symm
  cases a with
  | inl v =>
    apply Ray[e].point_ne_start (S.gaps e).first_outward vertices _ t
    exact strict.1
  | inr _ =>
    exact Ray[e].tail_ne_start (S.gaps e).first_outward (S.gaps e).first_nonzero t strict

private theorem contourGraftGapMark_horizontal (a : Attachment) (e : Event)
    (saved : e ∈ Stack a) (side : Bool) (t : Param a) :
    Cap.horizontal (Fold (some e) (Gap a e saved side t)) = Phys a t :=
  (congrArg Cap.horizontal (L.contourGraftPieceCollapse_gap_eq S a e saved side t)).trans
    (L.contourPhysicalAddress_side S a side t)

private theorem contourGraft_left_physical (slot : MetricGluing.BankStackSlot Stack) (t : Param slot.1) :
    Fold (Left slot t).1 (Left slot t).2 = (restore (Base slot.1 false t)).val := by
  obtain ⟨a, k⟩ := slot
  cases k using Fin.cases with
  | zero =>
    exact congrArg (fun y : MetricGluing.Total Pieces => Fold y.1 y.2)
      (MetricGluing.bankStackLeft_first Pieces Stack Base Gap a t)
  | succ i =>
    have at_gap := congrArg (fun y : MetricGluing.Total Pieces => Fold y.1 y.2)
      (MetricGluing.bankStackLeft_after Pieces Stack Base Gap a i t)
    exact at_gap.trans ((L.contourGraftPieceCollapse_gap_eq S a _ _ true t).trans
      (L.restore_contourBaseMark_sides S a t).symm)

private theorem contourGraft_fiberArc_at_mark (f : Graft → Space)
    (on_piece : ∀ y : MetricGluing.Total Pieces, f (Point y) = Fold y.1 y.2)
    (a : Attachment) (t : Param a) (strict : Strict a t) (e : Event) (saved : e ∈ Stack a) :
    ∃ P : Path (Gap a e saved false t) (Gap a e saved true t),
      Function.Injective P ∧
      {x | f (Point ⟨some e, x⟩) = (restore (Base a false t)).val} = Set.range P := by
  let address := Addr[a,e,saved,t]
  have gap := L.hasMarkedCollapseFibers_contourGraft S f on_piece e
  obtain ⟨P, covers, injective, _⟩ := (gap.2 address).1
  have geometry := injective (contourGap_strict_away S a t strict e saved)
  have first := contourGraftGapMark_eq_intrinsicAddressPoint S a e saved false t
  have last := contourGraftGapMark_eq_intrinsicAddressPoint S a e saved true t
  let Q := P.symm.cast first last
  have position := (L.contourGraftGapMark_spatial_eq_address S a e saved false t).symm.trans
    (L.contourGraftPieceCollapse_gap_eq S a e saved false t)
  refine ⟨Q, ?_, ?_⟩
  · exact geometry.comp unitInterval.symm_involutive.injective
  · change {x | f (Point ⟨some e, x⟩) = (restore (Base a false t)).val} = Set.range P.symm
    exact (congrArg (fun z : Space => {x | f (Point ⟨some e, x⟩) = z}) position.symm).trans
      (covers.trans P.symm_range.symm)

set_option maxHeartbeats 2400000 in
/-- The entire graft has a contractible collapse fiber over every point
strictly inside a finite cut edge or strictly past a terminal join. -/
theorem contourGraftCollapse_fiber_strict (f : Graft → Space)
    (on_piece : ∀ y : MetricGluing.Total Pieces, f (Point y) = Fold y.1 y.2)
    (b : Attachment) (t : Param b) (strict : Strict b t) :
    ContractibleSpace {z : Graft | f z = (restore (Base b false t)).val} := by
  let p := (restore (Base b false t)).val
  have canonical (a : Attachment) (s : Param a) (equal : Phys a s = Phys b t) :
      (⟨a, s⟩ : Σ a : Attachment, Param a) = ⟨b, t⟩ :=
    L.strictContourParameter_unique S b t strict a s equal
  have roof_sides := L.strictContourParameter_roof_sides_ne S b t strict
  have arcs (e : Event) (saved : e ∈ Stack b) :=
    L.contourGraft_fiberArc_at_mark S f on_piece b t strict e saved
  have gap_sides (e : Event) (saved : e ∈ Stack b) :
      Gap b e saved false t ≠ Gap b e saved true t := by
    intro same
    obtain ⟨P, injective, _⟩ := arcs e saved
    exact zero_ne_one (injective (P.source.trans (same.trans P.target.symm)))
  have unique : MetricGluing.BankStackUniqueMarksAt Stack Pieces Base Gap b t := by
    constructor
    · intro side a flag s same
      have position : Phys a s = Phys b t :=
        (L.contourPhysicalAddress_side S a flag s).symm.trans
          ((congrArg (fun x : L.whole.Cut => Cap.horizontal (restore x).val) same).trans
            (L.contourPhysicalAddress_side S b side t))
      have address := canonical a s position
      have at_b : a = b := congrArg Sigma.fst address
      subst a
      have time : s = t := eq_of_heq (Sigma.mk.inj address).2
      subst s
      refine ⟨?_, rfl⟩
      cases side <;> cases flag
      · rfl
      · exact (roof_sides same.symm).elim
      · exact (roof_sides same).elim
      · rfl
    · intro e saved side a another flag s same
      have position : Phys a s = Phys b t :=
        (L.contourGraftGapMark_horizontal S a e another flag s).symm.trans
          ((congrArg (fun x => Cap.horizontal (Fold (some e) x)) same).trans
            (L.contourGraftGapMark_horizontal S b e saved side t))
      have address := canonical a s position
      have at_b : a = b := congrArg Sigma.fst address
      subst a
      have time : s = t := eq_of_heq (Sigma.mk.inj address).2
      subst s
      refine ⟨?_, rfl⟩
      cases side <;> cases flag
      · rfl
      · exact (gap_sides e saved same.symm).elim
      · exact (gap_sides e saved same).elim
      · rfl
  have then_at (slot : MetricGluing.BankStackSlot Stack) (s : Param slot.1) :
      f (Point (Left slot s)) = (restore (Base slot.1 false s)).val :=
    (on_piece _).trans (L.contourGraft_left_physical S slot s)
  have on_slot (slot : MetricGluing.BankStackSlot Stack) (s : Param slot.1)
      (there : f (Point (Left slot s)) = p) :
      (⟨slot.1, s⟩ : Σ a : Attachment, Param a) = ⟨b, t⟩ :=
    canonical slot.1 s (congrArg Cap.horizontal ((then_at slot s).symm.trans there))
  have roof_fiber (x : L.whole.Cut) (on_fiber : f (Point ⟨none, x⟩) = p) :
      ∃ flag, x = Base b flag t := by
    have loc : Cap.horizontal (restore x).val = Phys b t :=
      congrArg Cap.horizontal ((on_piece ⟨none, x⟩).symm.trans on_fiber)
    have on_cut : x ∈ {x | Cap.horizontal (restore x).val ∈ R.wholeCarrier} := by
      change Cap.horizontal (restore x).val ∈ R.wholeCarrier
      rw [loc]
      exact L.contourGraftBaseMark_horizontal_mem_cut S b false t
    rw [← L.contourBaseMark_range_eq_cut S] at on_cut
    obtain ⟨a, member⟩ := Set.mem_iUnion.mp on_cut
    obtain ⟨flag, s, equal⟩ := Set.mem_iUnion.mp member
    have position : Phys a s = Phys b t :=
      (L.contourPhysicalAddress_side S a flag s).symm.trans
        ((congrArg (fun x : L.whole.Cut => Cap.horizontal (restore x).val) equal).trans loc)
    have address := canonical a s position
    have at_b : a = b := congrArg Sigma.fst address
    subst a
    have time : s = t := eq_of_heq (Sigma.mk.inj address).2
    subst s
    exact ⟨flag, equal.symm⟩
  have gap_fiber (e : Event) (x : Pieces (some e)) (on_fiber : f (Point ⟨some e, x⟩) = p) :
      e ∈ Stack b := by
    have marked := L.hasMarkedCollapseFibers_contourGraft S f on_piece e
    have location : p ∈ (Path[e]).carrier := on_fiber ▸ marked.1 (Set.mem_range_self x)
    obtain ⟨a, s, saved, there⟩ := L.exists_contourGraftSourcePath_attachment S e location
    have address := canonical a s (congrArg Cap.horizontal there)
    have bank : a = b := congrArg Sigma.fst address
    exact bank ▸ saved
  have nodup (a : Attachment) : (Stack a).Nodup := by
    cases a with
    | inl a => exact (D).contourSavedGapStack_nodup Selection S.contour a.val
    | inr a => exact (D).contourSavedGapStack_nodup Selection S.contour a.val
  exact MetricGluing.contractibleSpace_fiber_of_single_bank_stack Pieces Stack Base Gap b t f p
    (L.contourGraft_exact S) nodup unique on_slot (fun k => then_at ⟨b, k⟩ t)
    roof_fiber gap_fiber (fun i => arcs ((Stack b).get i) (List.get_mem _ _))

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
