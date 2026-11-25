module

public import Unfoldings.FewestNets.ThreeExitGraftProperCollapse
public import Unfoldings.Roof.CompletionOriginalPieces

/-! The collapse fiber outside the complete cut is a singleton. -/

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

local instance graftOffCutIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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
local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap

local notation "Attachment" => PotentialCutForest.ContourAttachment Fcut
local notation "Param" => PotentialCutForest.contourAttachmentParameter Fcut

local notation "restore" =>
  SpatialEnvelope.WholePartition.restoreCut L.whole.partition R.wholeCarrier
local notation "Path[" e "]" => PotentialCutForest.contourSourceSpatialRay Fcut S.contour S.starts e
local notation "Fold" => contourGraftPieceCollapse L S
local notation "Graft" => contourGraft L S
local notation "Banks" => MetricGluing.bankSeams Left Right
local notation "Surface" => SpatialEnvelope.wholeSurface M.plane

local notation "Q" => SpatialEnvelope.FloorMesh.roof T
  (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M S.higher)

set_option maxHeartbeats 1700000 in
/-- All the literal roof marks, including positive tail parameters, lie on the prescribed cut. -/
theorem contourGraftBaseMark_horizontal_mem_cut (a : Attachment) (side : Bool) (t : Param a) :
    Cap.horizontal (restore (Base a side t)).val ∈ R.wholeCarrier := by
  cases a with
  | inl v =>
    change Cap.horizontal (restore
      (L.contourParentMark S.higher S.contour S.starts v.val v.property side t)).val ∈ _
    rw [L.horizontal_contourParentMark S.higher S.contour S.starts]
    let x := AffineMap.lineMap ((Q).projectedVertex v.val)
      ((Q).projectedVertex ((Fcut).parents.parent v.val)) t.val
    let facing := (D).left ((Selection).edge v)
    have match_segment := (Q).projected_link_segment ((Selection).link v)
    have on_segment : x ∈ segment ℝ ((Q).projectedVertex v.val)
        ((Q).projectedVertex ((Fcut).parents.parent v.val)) :=
      lineMap_mem_segment ℝ _ _ t.property
    have on_edge : x ∈ ((Q).projectedTriangle facing.face).edge facing.edge :=
      match_segment.subset on_segment
    have included := (Fcut).selected_subset v on_edge
    have footprint : x ∈ (Q).footprint :=
      (Q).projectedTriangle_subset_footprint facing.face
        (((Q).projectedTriangle facing.face).edge_subset facing.edge on_edge)
    rw [(T).roof_footprint] at footprint
    exact (R.fineCut_mem_iff_whole level M S.higher footprint).mp included
  | inr edge =>
    let c := L.contourTerminalContinuation S.higher S.contour S.starts edge
    change Cap.horizontal (restore (c.mark side t)).val ∈ _
    obtain ⟨r, first, nonnegative, before, bank, label, _, _, _, restores, agrees⟩ :=
      L.exists_contourTerminalBanks S.higher S.contour S.starts edge
    let τ := R.exits.timeAtLevel level (R.exitRoot r)
    have τ_nonneg : 0 ≤ τ := nonnegative.trans (le_of_lt before)
    let mark := L.contourParentMark S.higher S.contour S.starts edge.val edge.property.1 side
    have ends (s : unitInterval) :
        Cap.horizontal (restore (mark s)).val =
          R.exits.ray (R.exitRoot r) (nonnegativeIntervalLineMap first τ nonnegative before.le s).val := by
      rw [show mark s = _ from agrees side s, restores, SpatialEnvelope.horizontal_point]
    have endpoint₀ : Cap.horizontal (restore (mark 0)).val =
        R.exits.ray (R.exitRoot r) first := by
      rw [ends]
      simp [nonnegativeIntervalLineMap]
    have endpoint₁ : Cap.horizontal (restore (mark 1)).val =
        R.exits.ray (R.exitRoot r) τ := by
      rw [ends]
      simp [nonnegativeIntervalLineMap]
    have position : Cap.horizontal (restore (c.mark side t)).val =
        R.exits.ray (R.exitRoot r) (τ + (τ - first) * t.val) := by
      rw [c.position, map_add, map_smul, map_sub, endpoint₀, endpoint₁]
      simp only [SlopeEnvelope.ExteriorPlan.ray]
      module
    rw [position]
    apply Set.mem_iUnion.mpr
    refine ⟨r.val, ?_⟩
    unfold ThreeExitComponentRouting.wholeCutPiece
    rw [dite_eq_left r.property]
    exact ⟨_, add_nonneg τ_nonneg (mul_nonneg (sub_nonneg.mpr before.le) t.property), rfl⟩

/-- A point of the original roof off the cut has exactly its single roof copy in the graft. -/
theorem contourGraftCollapse_fiber_off_cut (f : Graft → Space)
    (on_piece : ∀ y : MetricGluing.Total Pieces,
      f (MetricGluing.point Pieces Banks y) = Fold y.1 y.2)
    {p : Space} (inside : p ∈ Surface) (off_cut : Cap.horizontal p ∉ R.wholeCarrier) :
    ContractibleSpace {x : Graft | f x = p} := by
  obtain ⟨base, hb⟩ := L.whole.partition.restoreCut_surjective R.wholeCarrier ⟨p, inside⟩
  let root := MetricGluing.point Pieces Banks ⟨none, base⟩
  have at_root : f root = p :=
    (on_piece ⟨none, base⟩).trans (congrArg PolygonalPoint.val hb)
  have unique (x : Graft) (hx : f x = p) : x = root := by
    obtain ⟨⟨i, z⟩, rfl⟩ := MetricGluing.point_surjective Pieces Banks x
    have value := (on_piece ⟨i, z⟩).symm.trans hx
    cases i with
    | none =>
      have equal : restore z = restore base :=
        PolygonalPoint.ext (value.trans (congrArg PolygonalPoint.val hb).symm)
      have outside : Cap.horizontal (restore z).val ∉ R.wholeCarrier :=
        fun cut => off_cut ((congrArg Cap.horizontal value) ▸ cut)
      rw [L.whole.partition.restoreCut_injective_at R.wholeCarrier equal outside]
    | some e =>
      have member : p ∈ (Path[e]).carrier :=
        value ▸ (R.contourSourceGapCollapse level M S.higher S.contour S.starts e (S.gaps e) z).property
      obtain ⟨a, t, at_p⟩ := L.exists_contourGraftSourcePath_baseMark S e member
      exact (off_cut ((congrArg Cap.horizontal at_p) ▸
        L.contourGraftBaseMark_horizontal_mem_cut S a false t)).elim
  let : Nonempty {x : Graft | f x = p} := ⟨⟨root, at_root⟩⟩
  let : Subsingleton {x : Graft | f x = p} := ⟨fun x y =>
    Subtype.ext ((unique x.val x.property).trans (unique y.val y.property).symm)⟩
  infer_instance

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
