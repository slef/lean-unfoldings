module

public import Unfoldings.FewestNets.ThreeExitTerminalContinuation
public import Unfoldings.FewestNets.ThreeExitGapCollapse
public import Unfoldings.Roof.PotentialContourPhysicalLabels
public import Unfoldings.Roof.PotentialContourStack
public import Unfoldings.Roof.CompatibleContourSourceOnlyGraft

/-! The three-exit source gaps attach at the ordered marks of their actual physical cuts. -/

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

local instance contourGraftIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
    Fintype (T[h]).Index := @Fintype.ofFinite _ (T[h]).finite

/-- The actual saved contour of one affine-floor mesh. -/
structure SourceContour where
  higher : ∀ v : V, (G).height (pointOf v) < level
  contour : (D[higher]).BoundaryContour (F[higher]).retain
  starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots
  gaps : ∀ e : (D[higher]).PositiveContourSource Sel[higher] contour,
    OrientedBankGap ((F[higher]).contourSourceRay contour starts e)
      ((F[higher]).contourSourceOpenedRay contour starts e)

variable (S : SourceContour (R := R) (M := M) (level := level))

local notation "higher" => S.higher
local notation "contour" => S.contour
local notation "starts" => S.starts
local notation "T" => T[higher]
local notation "D" => D[higher]
local notation "Fcut" => F[higher]
local notation "Selection" => Sel[higher]

local notation "Attachment" => PotentialCutForest.ContourAttachment Fcut
local notation "Param" => PotentialCutForest.contourAttachmentParameter Fcut
local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "Stack" => PotentialCutForest.contourAttachmentStack Fcut contour
local notation "restore" => SpatialEnvelope.WholePartition.restoreCut L.whole.partition R.wholeCarrier
local notation "position" => fun v =>
  SpatialFolding.toSpace (SpatialEnvelope.FloorMesh.pairedFolding T) Set.univ
    (TriangleComplex.vertexPoint D Set.univ v)

/-- The base marks are the actual finite contour banks and their normalized whole tails. -/
def contourBaseMark : ∀ e : Attachment, Bool → Param e → L.whole.Cut
  | .inl v, side, t => L.contourParentMark higher contour starts v.val v.property side t
  | .inr e, side, t => (L.contourTerminalContinuation higher contour starts e).mark side t

local notation "Base" => contourBaseMark L S

/-- The finite parent bank and its normalized tail join at the same whole metric copy. -/
theorem contourBaseMark_tail_zero (edge : (D).ContourTerminalEdge Selection) (side : Bool) :
    Base (.inr edge) side 0 = Base (.inl ⟨edge.val, edge.property.1⟩) side 1 :=
  (L.contourTerminalContinuation higher contour starts edge).join side

/-- Both literal finite marks restore to their common spatial affine point. -/
theorem restore_contourParentMark_position (v : (D).Vertex Set.univ)
    (nonroot : v ∉ (Fcut).parents.roots) (side : Bool) (t : unitInterval) :
    (restore (L.contourParentMark higher contour starts v nonroot side t)).val =
      AffineMap.lineMap (position v) (position ((Fcut).parents.parent v)) t.val := by
  unfold contourParentMark
  rw [L.restore_fineMeshWholeMap]
  exact (T).pairedFolding.contourParentBank_position Selection contour (Fcut).boundary_roots
    starts v nonroot side t

/-- The two ends of any attachment have one and the same physical image. -/
theorem restore_contourBaseMark_sides (e : Attachment) (t : Param e) :
    (restore (Base e false t)).val = (restore (Base e true t)).val := by
  cases e with
  | inl v =>
    exact (L.restore_contourParentMark_position S v.val v.property false t).trans
      (L.restore_contourParentMark_position S v.val v.property true t).symm
  | inr e =>
    let C := L.contourTerminalContinuation higher contour starts e
    change (restore (C.mark false t)).val = (restore (C.mark true t)).val
    rw [C.position, C.position,
      L.restore_contourParentMark_position S e.val e.property.1 false 1,
      L.restore_contourParentMark_position S e.val e.property.1 true 1,
      L.restore_contourParentMark_position S e.val e.property.1 false 0,
      L.restore_contourParentMark_position S e.val e.property.1 true 0]

local notation "geometry" => S.gaps

local notation "models" => (fun e : Event => OrientedBankGap.model (geometry e))
local notation "Pieces" => polygonalBankStackPiece L.whole.Cut
  (fun e : Event => BankGapModel.region (OrientedBankGap.model (geometry e)))
local notation "Gap" => PotentialCutForest.contourGapMark Fcut contour starts models

/-- The actual graft inserts gaps in the saved contour order along every original bank. -/
abbrev contourGraft := MetricGluing.BankStackGraft (Pieces) Stack Base Gap

/-- On every piece, the spatial trace is its original roof placement or its marked gap collapse. -/
def contourGraftPieceCollapse : (i : Option Event) → Pieces i → Space
  | none, x => (restore x).val
  | some e, x => (R.contourSourceGapCollapse level M higher contour starts e (geometry e) x).val

local notation "Fold" => contourGraftPieceCollapse L S

/-- Each gap mark has the same spatial image as the base mark with that
attachment and parameter. This includes both endpoints of a finite edge and the whole tail. -/
theorem contourGraftPieceCollapse_gap_eq (a : Attachment) (e : Event)
    (member : e ∈ Stack a) (side : Bool) (t : Param a) :
    Fold (some e) (Gap a e member side t) = (restore (Base a side t)).val := by
  cases a with
  | inl v =>
    have prior := ((D).mem_contourSavedGapStack Selection contour v.val e).mp member
    have edge_member := ((D).mem_contourEdgeGapStack Selection contour v.val e).mpr prior
    change (R.contourSourceGapCollapse level M higher contour starts e (geometry e)
      ((geometry e).model.edgePoint (!side)
        ((D).contourGapBankIndex Selection contour v.val v.property e edge_member) t)).val = _
    rw [R.contourSourceGapCollapse_edgePoint]
    exact ((Fcut).contourSourceSpatialRay_point_contourParent contour starts e v.val v.property
      edge_member side t).trans (L.restore_fineMeshWholeMap higher _).symm
  | inr edge =>
    have prior := ((D).mem_contourSavedGapStack Selection contour edge.val e).mp member
    have edge_member := ((D).mem_contourEdgeGapStack Selection contour edge.val e).mpr prior
    let C := L.contourTerminalContinuation higher contour starts edge
    change (R.contourSourceGapCollapse level M higher contour starts e (geometry e)
      ((geometry e).model.tailPoint (!side) t)).val = (restore (C.mark side t)).val
    rw [R.contourSourceGapCollapse_tailPoint,
      (Fcut).contourSourceSpatialRay_tail_eq_terminalParent contour starts e edge edge_member,
      C.position, L.restore_contourParentMark_position S edge.val edge.property.1 side 1,
      L.restore_contourParentMark_position S edge.val edge.property.1 side 0]
    simp [SpatialEnvelope.FloorMesh.roof]

/-- Every seam of the ordered bank stack preserves the exact spatial collapse point. -/
theorem contourGraftPieceCollapse_seam (slot : MetricGluing.BankStackSlot Stack) (t : Param slot.1) :
    let first := MetricGluing.bankStackLeft Pieces Stack Base Gap slot t
    let last := MetricGluing.bankStackRight Pieces Stack Base Gap slot t
    Fold first.1 first.2 = Fold last.1 last.2 := by
  classical
  change _ = _
  have left : let p := MetricGluing.bankStackLeft Pieces Stack Base Gap slot t
      Fold p.1 p.2 = (restore (Base slot.1 false t)).val := by
    unfold MetricGluing.bankStackLeft
    split
    · rfl
    · exact (L.contourGraftPieceCollapse_gap_eq S slot.1 _ _ true t).trans
        (L.restore_contourBaseMark_sides S slot.1 t).symm
  have right : let p := MetricGluing.bankStackRight Pieces Stack Base Gap slot t
      Fold p.1 p.2 = (restore (Base slot.1 false t)).val := by
    unfold MetricGluing.bankStackRight
    split
    · exact L.contourGraftPieceCollapse_gap_eq S slot.1 _ _ false t
    · exact (L.restore_contourBaseMark_sides S slot.1 t).symm
  exact left.trans right.symm

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
