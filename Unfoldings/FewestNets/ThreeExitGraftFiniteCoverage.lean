module

public import Unfoldings.FewestNets.ThreeExitGraftOffCutFiber
public import Unfoldings.Roof.AffineFloorCutBoundary
public import Unfoldings.Complex.ContourParentMarkCoverage

/-! Every cut roof copy strictly within the finite section has a named parent bank. -/

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

local instance graftBelowWindowIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
    Fintype (T[h]).Index := @Fintype.ofFinite _ (T[h]).finite

variable (S : SourceContour (R := R) (M := M) (level := level))

local notation "T" => T[S.higher]
local notation "D" => D[S.higher]
local notation "Fcut" => F[S.higher]
local notation "Selection" => Sel[S.higher]
local notation "Retain" => PotentialCutForest.retain Fcut
local notation "Fold" => SpatialEnvelope.FloorMesh.pairedFolding T
local notation "restore" =>
  SpatialEnvelope.WholePartition.restoreCut L.whole.partition R.wholeCarrier
local notation "floor" => SlopeEnvelope.FiniteSlopeModel.referenceFloor B.reference
local notation "section" => SpatialEnvelope.clipAbove M.plane floor (-level)

local instance finiteCoverageVertexFintype : Fintype V := Fintype.ofFinite _

private theorem exists_fine_cut_seam_at (p : Plane)
    (cut : p ∈ R.wholeCarrier) (below : (G).height p < level) :
    ∃ s : (D).Seam, s ∉ Retain ∧ p ∈ ((T).projectedTriangle ((D).left s).face).edge
      ((D).left s).edge := by
  let initial := fineMeshCutFirst (K := K) (slopes := slopes) (seed := seed)
  let terminal := R.fineMeshCutLast level
  have inside : p ∈ interior section := by
    rw [M.clipAbove_referenceFloor_eq]
    exact (G).mem_interior_sublevel below
  have covered := (R.fineCut_mem_iff_whole level M S.higher (interior_subset inside)).mpr cut
  rw [R.fineMesh_cuts_eq_segments level S.higher] at covered
  obtain ⟨i, on_segment⟩ := Set.mem_iUnion.mp covered
  have first : initial i ∈ section := by
    rw [M.clipAbove_referenceFloor_eq]
    exact (S.higher _).le
  have last : terminal i ∈ section := by
    rw [M.clipAbove_referenceFloor_eq]
    exact R.cutLast_height_le level S.higher _
  have cover := (T).prescribed_edge_cover initial terminal
    (fun i => R.fineMeshCutEndpoints_ne level i S.higher) i first last
  obtain ⟨e, on_edge⟩ := Set.mem_iUnion.mp (cover.subset on_segment)
  let ref : EdgeRef (T).Index := ⟨e.val.1, e.val.2⟩
  obtain ⟨s, at_seam⟩ := (T).exists_seam_of_projected_edge_interior
    (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M S.higher) ref
    on_edge inside
  have edge_eq : ((T).projectedTriangle ((D).left s).face).edge ((D).left s).edge =
      ((T).projectedTriangle e.val.1).edge e.val.2 := by
    rcases at_seam with left | right
    · change ref = (D).left s at left
      rw [← left]
    · change ref = (D).right s at right
      rw [(T).paired_seam_projected_edge s, ← right]
  refine ⟨s, ?_, edge_eq.symm.subset on_edge⟩
  rw [R.fineMesh_retain_eq_wholeCut]
  intro retained
  apply retained
  rw [edge_eq]
  intro q hq
  have finite : q ∈ FiniteEmbeddedGraph.carrier (R.truncatedEmbedding level S.higher) := by
    rw [R.fineMesh_cuts_eq_segments level S.higher]
    exact Set.mem_iUnion.mpr ⟨i, e.property hq⟩
  have section_q : q ∈ section := (T).cover.symm.subset
    (Set.mem_iUnion.mpr ⟨e.val.1, ((T).projectedTriangle e.val.1).edge_subset e.val.2 hq⟩)
  exact (R.fineCut_mem_iff_whole level M S.higher section_q).mp finite

set_option maxHeartbeats 1450000 in
/-- Every original roof copy below the affine truncation has a genuine contour-bank name. -/
theorem exists_contourParentMark_of_cut_below (x : L.whole.Cut)
    (cut : Cap.horizontal (restore x).val ∈ R.wholeCarrier)
    (below : (G).height (Cap.horizontal (restore x).val) < level) :
    ∃ (v : {v : (D).Vertex Set.univ // v ∉ (Fcut).parents.roots}) (side : Bool) (t : unitInterval),
      L.contourParentMark S.higher S.contour S.starts v.val v.property side t = x := by
  let p := Cap.horizontal (restore x).val
  obtain ⟨y, mapped, _⟩ := L.exists_fineMesh_ball_chart S.higher x below
  have position : Cap.horizontal ((Fold).toSpace Retain y) = p :=
    (congrArg Cap.horizontal (L.restore_fineMeshWholeMap S.higher y)).symm.trans
      (congrArg (fun z => Cap.horizontal (restore z).val) mapped)
  obtain ⟨s, removed, on_edge⟩ := exists_fine_cut_seam_at S p cut below
  let left := (D).left s
  let q := ((T).edgeProjection left.face left.edge).symm ⟨p, on_edge⟩
  have q_pos : Cap.horizontal ((Fold).place left.face q.val) = p :=
    ((M.plane ((T).support left.face)).horizontal_place q.val).trans
      ((M.plane ((T).support left.face)).project.apply_symm_apply p)
  have boundary := (T).mem_bankBoundary_of_projected_cut_edge Retain s removed q y
    (position.trans q_pos.symm)
  obtain ⟨bank, z, rfl⟩ := Set.mem_iUnion.mp boundary
  rcases (D).relativeBank_cases Retain Set.univ bank with rim | ⟨seam, bit, name⟩
  · have frontier := (T).projected_original_bank_frontier
      (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M S.higher)
      ⟨bank.val, rim⟩ z
    change Cap.horizontal ((Fold).place bank.val.face z.val) = p at position
    rw [position] at frontier
    have inside : p ∈ interior section := by
      rw [M.clipAbove_referenceFloor_eq]
      exact (G).mem_interior_sublevel below
    exact (frontier.2 inside).elim
  · obtain ⟨v, side, t, equal⟩ := (D).exists_contourParentMark_of_relativeCutBank
      Selection S.contour (Fcut).boundary_roots S.starts seam bit bank name z
    exact ⟨v, side, t, (congrArg (L.fineMeshWholeMap S.higher) equal).trans mapped⟩

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
