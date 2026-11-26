module

public import Unfoldings.FewestNets.ThreeExitGraftDevelopment
public import Unfoldings.FewestNets.ThreeExitOriginalDevelopment


/-! The faithfully developed graft gives a net along original edges. -/

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

local instance graftOriginalNetIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams Left Right

local notation "Exit" => TriangleComplex.ContourTerminalEdge D Selection
local notation "Child" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Graft" => contourGraft L S
local notation "Point" => MetricGluing.point Pieces Banks
local notation "Fold" => contourGraftPieceCollapse L S
local notation "Surface" => SpatialEnvelope.wholeSurface M.plane
local notation "restore" => SpatialEnvelope.WholePartition.restoreCut L.whole.partition R.wholeCarrier
local notation "Phys" => contourPhysicalAddress L S
local notation "Q" => SpatialEnvelope.FloorMesh.roof T
  (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M S.higher)
/-- The developed original roof is locally isometric away from the cuts. Points
that coincide in the layout restore to the same physical point. -/
theorem exists_contourGraft_roof_layout (develop : Graft → Plane)
    (rigid : Isometry develop) (onto : Function.Surjective develop) :
    ∃ layout : L.whole.Cut → Plane, Continuous layout ∧
      (∀ x y, layout x = layout y → (restore x).val = (restore y).val) ∧
      ∀ x : L.whole.Cut, Cap.horizontal (restore x).val ∉ R.wholeCarrier →
        ∃ r > 0, Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => layout y.val) := by
  obtain ⟨collapse, proper, _, on_piece⟩ := L.exists_contourGraftProperCollapse S
  let A : Graft ≃ᵢ Plane := ⟨Equiv.ofBijective develop ⟨rigid.injective, onto⟩, rigid⟩
  let layout (x : L.whole.Cut) := develop (Point ⟨none, x⟩)
  have roof (x : L.whole.Cut) : collapse (Point ⟨none, x⟩) = (restore x).val :=
    on_piece ⟨none, x⟩
  refine ⟨layout, rigid.continuous.comp (MetricGluing.of_lipschitz Pieces Banks none).continuous,
    ?_, ?_⟩
  · intro x y equal
    exact (roof x).symm.trans ((congrArg collapse (rigid.injective equal)).trans (roof y))
  intro x outside
  have attached {b c : MetricGluing.Total Pieces} (joined : Banks b c) :
      Cap.horizontal (collapse (Point b)) ∈ R.wholeCarrier := by
    obtain ⟨slot, t, rfl, rfl⟩ := joined
    have value := (on_piece _).trans (L.contourGraft_left_physical S slot t)
    rw [value]
    exact L.contourGraftBaseMark_horizontal_mem_cut S slot.1 false t
  let p (y : Plane) := Cap.horizontal (collapse (A.symm y))
  have cont : Continuous p := Cap.horizontalCLM.continuous.comp
    (proper.continuous.comp A.symm.continuous)
  let outsideCut := p ⁻¹' (R.wholeCarrier)ᶜ
  have open_U : IsOpen outsideCut := R.isClosed_wholeCarrier.isOpen_compl.preimage cont
  have in_U : layout x ∈ outsideCut := by
    change Cap.horizontal (collapse (A.symm (A (Point ⟨none, x⟩)))) ∉ R.wholeCarrier
    rw [A.symm_apply_apply, roof]
    exact outside
  obtain ⟨δ, δpos, free⟩ := Metric.isOpen_iff.mp open_U (layout x) in_U
  have distant (b c : MetricGluing.Total Pieces) (joined : Banks b c) :
      ENNReal.ofReal δ ≤ edist (Point ⟨none, x⟩) (Point b) := by
    apply le_of_not_gt
    intro near
    rw [← A.isometry.edist_eq (Point ⟨none, x⟩) (Point b), edist_comm, edist_dist] at near
    have in_ball : A (Point b) ∈ Metric.ball (layout x) δ :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp near
    have hn := free in_ball
    change Cap.horizontal (collapse (A.symm (A (Point b)))) ∉ R.wholeCarrier at hn
    rw [A.symm_apply_apply] at hn
    exact hn (attached joined)
  refine ⟨δ / 3, div_pos δpos (by norm_num), ?_⟩
  exact rigid.comp (MetricGluing.of_isometry_on_ball_of_no_seams Pieces Banks none x δpos distant)

/-- A global development of the completed source graft yields an original-edge
net for the selected connected component. -/
theorem hasOriginalEdgeNet_of_contourGraft_isometry (selected : K.normalSlope seed ∈ slopes)
    (develop : Graft → Plane) (rigid : Isometry develop) (onto : Function.Surjective develop) :
    C.HasOriginalEdgeNet U := by
  obtain ⟨layout, continuous_layout, faithful, local_layout⟩ :=
    L.exists_contourGraft_roof_layout S develop rigid onto
  exact R.hasOriginalEdgeNet_of_whole_cut_layout M selected L.whole layout
    continuous_layout faithful local_layout

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
