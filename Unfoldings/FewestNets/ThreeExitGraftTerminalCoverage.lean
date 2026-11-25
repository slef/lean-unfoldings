module

public import Unfoldings.FewestNets.ThreeExitGraftFiniteCoverage

/-! The actual continued marks exhaust all cut roof copies at and beyond the affine floor. -/

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

local instance graftTerminalCoverageIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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
local notation "A" => R.stems.choice.parents
local notation "Root" => {v : V // v ∈ AscendingParents.roots A}
local notation "Child" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Exit" => TriangleComplex.ContourTerminalEdge D Selection
local notation "Q" => SpatialEnvelope.FloorMesh.roof T
  (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M S.higher)
local notation "Mark" => L.contourParentMark S.higher S.contour S.starts

private theorem parentStart_below (e : Child) :
    (G).height ((Q).projectedVertex e.val) < level := by
  obtain ⟨seg⟩ := R.fineMesh_parent_alignment level M S.higher e.val e.property
  obtain ⟨⟨v | r, valid⟩, s, t, s_mem, t_mem, advance, at_s, _⟩ := seg
  · change AffineMap.lineMap (pointOf v) (R.cutLast level v) s = _ at at_s
    by_cases start : s = 0
    · rw [start, AffineMap.lineMap_apply_zero] at at_s
      exact at_s ▸ S.higher v
    · apply R.truncatedSegment_height_lt level S.higher v
      rw [← at_s]
      exact lineMap_mem_openSegment ℝ _ _
        ⟨lt_of_le_of_ne s_mem.1 (Ne.symm start), advance.trans_le t_mem.2⟩
  · exact (valid ⟨r, rfl⟩).elim

private theorem everyParentEnd_le (e : Child) :
    (G).height ((Q).projectedVertex ((Fcut).parents.parent e.val)) ≤ level := by
  have position := (Q).projectedVertex_mem_footprint ((Fcut).parents.parent e.val)
  rw [(T).roof_footprint, M.clipAbove_referenceFloor_eq] at position
  exact position

include L in
set_option maxHeartbeats 1900000 in
/-- Every original exit has a selected fine seam ending exactly at its truncation point. -/
theorem exists_contourTerminalEdge_at_exit (r : Root) :
    ∃ e : Exit, (Q).projectedVertex ((Fcut).parents.parent e.val) =
      R.exits.pointAtLevel level (R.exitRoot r) := by
  let head (e : Child) := (Q).projectedVertex e.val
  let tip (e : Child) := (Q).projectedVertex ((Fcut).parents.parent e.val)
  let E := ⋃ e : Child, segment ℝ (head e) (tip e)
  have closed : IsClosed E := isClosed_iUnion_of_finite fun e => by
    rw [segment_eq_image_lineMap]
    have line : Continuous (fun t : ℝ => AffineMap.lineMap (head e) (tip e) t) := by
      simp only [AffineMap.lineMap_apply_module']
      fun_prop
    exact (isCompact_Icc.image line).isClosed
  let ray (t : ℝ) := R.exits.ray (R.exitRoot r) t
  let τ := R.exits.timeAtLevel level (R.exitRoot r)
  have τ_pos : 0 < τ := R.exits.timeAtLevel_pos level _ (R.exit_origin_below level S.higher r)
  have height := R.exits.pointAtLevel_height level _ (R.exit_origin_below level S.higher r)
  change (G).height (ray τ) = level at height
  have continuous_ray : Continuous ray := by unfold ray SlopeEnvelope.ExteriorPlan.ray; fun_prop
  have cover : Set.Ioo 0 τ ⊆ ray ⁻¹' E := by
    intro t ht
    have ht_mem : 0 ≤ t := ht.1.le
    have below : (G).height (ray t) < level := by
      rw [show level = (G).height (ray τ) from height.symm]
      simp only [ray, R.exits.height_ray _ ht_mem, R.exits.height_ray _ τ_pos.le]
      exact add_lt_add_right (mul_lt_mul_of_pos_right ht.2 (R.exits.positive (R.exitRoot r))) _
    let p : PolygonalPoint (SpatialEnvelope.wholeSurface M.plane) :=
      ⟨SpatialEnvelope.point M.plane (ray t), ⟨ray t, rfl⟩⟩
    obtain ⟨x, x_eq⟩ := L.whole.restore_surjective p
    have at_x : Cap.horizontal (restore x).val = ray t := by
      rw [x_eq]
      exact SpatialEnvelope.horizontal_point M.plane _
    have cut : Cap.horizontal (restore x).val ∈ R.wholeCarrier := by
      rw [at_x]
      apply Set.mem_iUnion.mpr
      refine ⟨r.val, ?_⟩
      unfold ThreeExitComponentRouting.wholeCutPiece
      rw [dite_eq_left r.property]
      exact ⟨t, ht.1.le, rfl⟩
    obtain ⟨e, side, u, mark⟩ := L.exists_contourParentMark_of_cut_below S x cut (at_x.symm ▸ below)
    have on_segment := lineMap_mem_segment ℝ (head e) (tip e) u.property
    have projected := L.horizontal_contourParentMark S.higher S.contour S.starts e.val e.property side u
    rw [mark, at_x] at projected
    exact Set.mem_iUnion.mpr ⟨e, projected.symm ▸ on_segment⟩
  have at_limit : τ ∈ closure (Set.Ioo 0 τ) := by
    rw [closure_Ioo (Ne.symm τ_pos.ne')]
    exact ⟨τ_pos.le, le_rfl⟩
  have hits : ray τ ∈ E := closure_minimal cover (closed.preimage continuous_ray) at_limit
  obtain ⟨e, contact⟩ := Set.mem_iUnion.mp hits
  obtain ⟨t, bounds, at_point⟩ := (segment_eq_image_lineMap ℝ _ _).subset contact
  have at_end : t = 1 := by
    by_contra end_ne
    have lt : (G).height (ray τ) < level := by
      by_cases start : t = 0
      · rw [start, AffineMap.lineMap_apply_zero] at at_point
        exact at_point ▸ parentStart_below S e
      · refine (G).openSegment_height_lt (parentStart_below S e) (everyParentEnd_le S e) ?_
        rw [openSegment_eq_image_lineMap]
        exact ⟨t, ⟨lt_of_le_of_ne bounds.1 (Ne.symm start), lt_of_le_of_ne bounds.2 end_ne⟩, at_point⟩
    exact lt.ne height
  rw [at_end, AffineMap.lineMap_apply_one] at at_point
  have parent_root : (Fcut).parents.parent e.val ∈ (Fcut).parents.roots := by
    by_contra nonroot
    have strict := parentStart_below S ⟨(Fcut).parents.parent e.val, nonroot⟩
    exact strict.ne ((congrArg (G).height at_point).trans height)
  exact ⟨⟨e.val, e.property, parent_root⟩, at_point⟩

set_option maxHeartbeats 2200000 in
/-- At and beyond the floor, every cut roof point has a literal continued bank mark. -/
theorem exists_contourTailMark_of_cut_above (x : L.whole.Cut)
    (cut : Cap.horizontal (restore x).val ∈ R.wholeCarrier)
    (above : level ≤ (G).height (Cap.horizontal (restore x).val)) :
    ∃ (e : Exit) (side : Bool) (t : ℝ≥0),
      (L.contourTerminalContinuation S.higher S.contour S.starts e).mark side t = x := by
  classical
  let p := Cap.horizontal (restore x).val
  change p ∈ R.wholeCarrier at cut
  obtain ⟨v, member⟩ := Set.mem_iUnion.mp cut
  by_cases root : v ∈ (A).roots
  swap
  · unfold ThreeExitComponentRouting.wholeCutPiece at member
    rw [dite_eq_right root] at member
    have convex : Convex ℝ {q | (G).height q < level} := by
      simpa only [Set.mem_univ, true_and] using (G).convex_height.convex_lt level
    exact (above.not_gt (convex.segment_subset (S.higher v) (S.higher ((A).parent v)) member)).elim
  let r : Root := ⟨v, root⟩
  unfold ThreeExitComponentRouting.wholeCutPiece at member
  rw [dite_eq_left root] at member
  obtain ⟨s, nonnegative, loc⟩ := member
  change p = R.exits.ray (R.exitRoot r) s at loc
  obtain ⟨e, end_eq⟩ := L.exists_contourTerminalEdge_at_exit S r
  obtain ⟨r', first, first_nonneg, before, banks, sides, _, _, _, restores, agrees⟩ :=
    L.exists_contourTerminalBanks S.higher S.contour S.starts e
  let τ' := R.exits.timeAtLevel level (R.exitRoot r')
  let endTime : ℝ≥0 := ⟨τ', first_nonneg.trans before.le⟩
  have one : nonnegativeIntervalLineMap first τ' first_nonneg before.le 1 = endTime :=
    Subtype.ext (by simp [nonnegativeIntervalLineMap, endTime])
  have named : Mark e.val e.property.1 false 1 = banks (sides false) endTime :=
    (agrees false 1).trans (congrArg (banks (sides false)) one)
  have value := ((congrArg (fun x => (restore x).val) named).trans (restores false endTime))
  have position : Cap.horizontal (restore (Mark e.val e.property.1 false 1)).val =
      R.exits.pointAtLevel level (R.exitRoot r') :=
    (congrArg Cap.horizontal value).trans (SpatialEnvelope.horizontal_point M.plane _)
  have end_coord := L.horizontal_contourParentMark S.higher S.contour S.starts e.val e.property.1 false 1
  rw [show (1 : unitInterval).val = 1 from rfl, AffineMap.lineMap_apply_one] at end_coord
  have same : r' = r := Sum.inr.inj (R.truncatedPoint_injective level S.higher
    (show R.truncatedPoint level (.inr r') = R.truncatedPoint level (.inr r) from
      (position.symm.trans (end_coord.trans end_eq))))
  subst r'
  let τ := R.exits.timeAtLevel level (R.exitRoot r)
  have τ_pos : 0 < τ := R.exits.timeAtLevel_pos level _ (R.exit_origin_below level S.higher r)
  have high : (G).height (R.exits.ray (R.exitRoot r) τ) = level :=
    R.exits.pointAtLevel_height level _ (R.exit_origin_below level S.higher r)
  have time_order : τ ≤ s := by
    have h : level ≤ (G).height (R.exits.ray (R.exitRoot r) s) :=
      (congrArg (G).height loc) ▸ above
    rw [R.exits.height_ray _ τ_pos.le] at high
    rw [R.exits.height_ray _ nonnegative] at h
    have scaled : τ * R.exits.rate (R.exitRoot r) ≤ s * R.exits.rate (R.exitRoot r) := by
      linarith only [h, high]
    exact le_of_mul_le_mul_right scaled (R.exits.positive (R.exitRoot r))
  let t : ℝ≥0 := ⟨(s - τ) / (τ - first),
    div_nonneg (sub_nonneg.mpr time_order) (sub_nonneg.mpr before.le)⟩
  let c := L.contourTerminalContinuation S.higher S.contour S.starts e
  have mark_point (side : Bool) (u : unitInterval) :
      Cap.horizontal (restore (Mark e.val e.property.1 side u)).val =
        R.exits.ray (R.exitRoot r) (nonnegativeIntervalLineMap first τ first_nonneg before.le u).val := by
    rw [agrees, restores, SpatialEnvelope.horizontal_point]
  have left (side : Bool) :
      Cap.horizontal (restore (Mark e.val e.property.1 side 0)).val =
        R.exits.ray (R.exitRoot r) first := by
    rw [mark_point]
    simp [nonnegativeIntervalLineMap]
  have right (side : Bool) :
      Cap.horizontal (restore (Mark e.val e.property.1 side 1)).val =
        R.exits.ray (R.exitRoot r) τ := by
    rw [mark_point]
    simp [nonnegativeIntervalLineMap]
  have same_pos (side : Bool) : Cap.horizontal (restore (c.mark side t)).val = p := by
    rw [c.position, map_add, map_smul, map_sub, left, right, loc]
    have normalized : τ + (τ - first) * t.val = s := by
      change τ + (τ - first) * ((s - τ) / (τ - first)) = s
      rw [mul_comm (τ - first), div_mul_cancel₀ _ (sub_pos.mpr before).ne']
      ring
    rw [← normalized]
    simp only [SlopeEnvelope.ExteriorPlan.ray]
    module
  let time : ℝ≥0 := ⟨s, nonnegative⟩
  have time_pos : 0 < time.val := τ_pos.trans_le time_order
  obtain ⟨pair, _, _, _, _, exhaust, _⟩ := L.whole.exists_exit_banks_with_charts r
  obtain ⟨flag, at_x⟩ := exhaust time time_pos x loc
  have recovered (side : Bool) : ∃ flag, c.mark side t = pair flag time :=
    exhaust time time_pos (c.mark side t) ((same_pos side).trans loc)
  choose label named using recovered
  have injective : Function.Injective label := by
    intro i j equal
    by_contra distinct
    exact c.disjoint i j distinct t t ((named i).trans (equal ▸ (named j).symm))
  obtain ⟨side, side_eq⟩ := (Finite.injective_iff_surjective.mp injective) flag
  exact ⟨e, side, t, (named side).trans ((congrArg (fun b => pair b time) side_eq).trans at_x.symm)⟩

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
