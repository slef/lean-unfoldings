module

public import Unfoldings.FewestNets.ThreeExitGraftTerminalJoinClasses

/-! Every whole graft fiber over an affine-floor terminal join is a single chain of arcs. -/

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

local instance graftTerminalFiberIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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
local notation "Point" => MetricGluing.point Pieces Banks

set_option maxHeartbeats 2000000 in
/-- Over the join of the finite window and the true tail, both parameter
names give the same contractible fiber in the full metric graft. -/
theorem contourGraftCollapse_fiber_terminalJoin (f : Graft → Space)
    (on_piece : ∀ y : MetricGluing.Total Pieces, f (Point y) = Fold y.1 y.2) (e : Exit) :
    ContractibleSpace {z : Graft | f z = (restore (Base (.inr e) false 0)).val} := by
  let b : Attachment := .inr e
  let p := (restore (Base b false 0)).val
  have then_at (slot : BankStackSlot Stack) (s : Param slot.1) :
      f (Point (Left slot s)) = (restore (Base slot.1 false s)).val :=
    (on_piece _).trans (L.contourGraft_left_physical S slot s)
  have seam_names {x y : MetricGluing.Total Pieces} (joined : Banks x y)
      (on_fiber : f (Point x) = p) : ∃ k : Fin ((Stack b).length + 1),
        x = Left TailSlot[e,k] 0 ∧ y = Right TailSlot[e,k] 0 := by
    obtain ⟨⟨a, i⟩, t, rfl, rfl⟩ := joined
    have location : Phys a t = Phys b 0 :=
      congrArg Cap.horizontal ((then_at ⟨a, i⟩ t).symm.trans on_fiber)
    rcases L.contourPhysicalAddress_eq_terminalJoin S e a t location with finite | tail
    · have tag : a = .inl Child[e] := congrArg Sigma.fst finite
      subst a
      have time : t = 1 := eq_of_heq (Sigma.mk.inj finite).2
      subst t
      exact ⟨i, L.contourGraft_terminalJoin_endpoint S e i false,
        L.contourGraft_terminalJoin_endpoint S e i true⟩
    · have tag : a = .inr e := congrArg Sigma.fst tail
      subst a
      have time : t = 0 := eq_of_heq (Sigma.mk.inj tail).2
      subst t
      exact ⟨i, rfl, rfl⟩
  have roof_fiber (x : L.whole.Cut) (on_fiber : f (Point ⟨none, x⟩) = p) :
      ∃ side, x = Base b side 0 := by
    have location : Cap.horizontal (restore x).val = Phys b 0 :=
      congrArg Cap.horizontal ((on_piece ⟨none, x⟩).symm.trans on_fiber)
    have cut : x ∈ {x | Cap.horizontal (restore x).val ∈ R.wholeCarrier} := by
      change Cap.horizontal (restore x).val ∈ R.wholeCarrier
      rw [location]
      exact L.contourGraftBaseMark_horizontal_mem_cut S b false 0
    rw [← L.contourBaseMark_range_eq_cut S] at cut
    obtain ⟨a, member⟩ := Set.mem_iUnion.mp cut
    obtain ⟨side, t, equal⟩ := Set.mem_iUnion.mp member
    have at_a : Phys a t = Phys b 0 :=
      (L.contourPhysicalAddress_side S a side t).symm.trans
        ((congrArg (fun z : L.whole.Cut => Cap.horizontal (restore z).val) equal).trans location)
    let mark (q : Σ a : Attachment, Param a) := Base q.1 side q.2
    rcases L.contourPhysicalAddress_eq_terminalJoin S e a t at_a with finite | tail
    · exact ⟨side, (equal.symm.trans (congrArg mark finite)).trans
        (L.contourBaseMark_tail_zero S e side).symm⟩
    · exact ⟨side, equal.symm.trans (congrArg mark tail)⟩
  have gap_fiber (g : Event) (x : Pieces (some g)) (on_fiber : f (Point ⟨some g, x⟩) = p) :
      g ∈ Stack b := by
    have marked := L.hasMarkedCollapseFibers_contourGraft S f on_piece g
    have location : p ∈ (Path[g]).carrier := on_fiber ▸ marked.1 (Set.mem_range_self x)
    obtain ⟨a, t, saved, there⟩ := L.exists_contourGraftSourcePath_attachment S g location
    rcases L.contourPhysicalAddress_eq_terminalJoin S e a t (congrArg Cap.horizontal there) with
      finite | tail
    · have tag : a = .inl Child[e] := congrArg Sigma.fst finite
      have at_end : g ∈ Stack (.inl Child[e]) :=
        Eq.mp (congrArg (fun a : Attachment => g ∈ Stack a) tag) saved
      exact at_end
    · have tag : a = .inr e := congrArg Sigma.fst tail
      exact Eq.mp (congrArg (fun a : Attachment => g ∈ Stack a) tag) saved
  apply MetricGluing.contractibleSpace_fiber_of_bank_stack_pairs Pieces Stack Base Gap b 0 f p
    (L.contourGraft_exact S) (contourGraft_stack_nodup S)
    (L.contourGraft_terminalJoin_eqvGen_pair S e) seam_names
    (fun k => then_at TailSlot[e,k] 0) roof_fiber gap_fiber
  intro i
  exact L.contourGraft_fiberArc_at_mark S f on_piece b 0 ((Stack b).get i) (List.get_mem _ _)
    (contourGraftGap_tail_zero_ne_start S ((Stack b).get i))

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
