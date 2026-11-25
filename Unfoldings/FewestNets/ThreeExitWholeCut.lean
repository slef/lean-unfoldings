module

public import Unfoldings.FewestNets.ThreeExitEmbedding
public import Unfoldings.Convex.FiniteSlopeModel
public import Unfoldings.Geometry.SpatialEnvelopeCut
public import Unfoldings.Geometry.SegmentEquation
public import Mathlib.Tactic.FinCases

/-! The actual unbounded cut extends each leaf of the finite three-exit mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope.ExteriorPlan

variable {E : SlopeEnvelope} {I : Type*} (P : E.ExteriorPlan I)

theorem closed_ray_inter_sublevel (i : I) {level : ℝ} (higher : E.height (P.point i) < level) :
    {x | ∃ t : ℝ, 0 ≤ t ∧ x = P.ray i t} ∩ {x | E.height x ≤ level} =
      segment ℝ (P.point i) (P.pointAtLevel level i) := by
  rw [segment_eq_image_lineMap]
  ext x
  have time_pos := P.timeAtLevel_pos level i higher
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, reaches⟩
    have before : t ≤ P.timeAtLevel level i := by
      unfold timeAtLevel
      apply (le_div_iff₀ (show 0 < P.rate i from P.positive i)).2
      change E.height (P.ray i t) ≤ level at reaches
      rw [P.height_ray i ht] at reaches
      linarith only [reaches]
    refine ⟨t / P.timeAtLevel level i, ⟨div_nonneg ht time_pos.le, (div_le_one₀ time_pos).2 before⟩,
      ?_⟩
    rw [P.lineMap_pointAtLevel, div_mul_cancel₀ _ time_pos.ne']
  · rintro ⟨t, ht, rfl⟩
    rw [P.lineMap_pointAtLevel]
    have t_nonneg := mul_nonneg ht.1 time_pos.le
    refine ⟨⟨_, t_nonneg, rfl⟩, ?_⟩
    have before : t * P.timeAtLevel level i ≤ P.timeAtLevel level i := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 time_pos.le
    change E.height (P.ray i (t * P.timeAtLevel level i)) ≤ level
    calc
      _ ≤ E.height (P.pointAtLevel level i) := by
        rw [pointAtLevel, P.height_ray i t_nonneg, P.height_ray i time_pos.le]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right before (P.positive i).le)
      _ = level := P.pointAtLevel_height level i higher

end Unfoldings.SlopeEnvelope.ExteriorPlan

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : FewestNets.ThreeExitStemWindows}
  (R : K.ThreeExitComponentRouting seed B compact nonempty H)

local notation "U" => K.selectionComponent slopes seed
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ K.restrictedCarrier U}
local notation "A" => R.stems.choice.parents
local notation "G₀" => K.componentClippedExtension
  (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty
local notation "G" => SlopeEnvelope.recenter (G₀) B.reference
local notation "p" => (fun v : V => K.projectedVertex (Subtype.val v))

open Classical in
/-- The complete piece along a selected original seam or an assigned exterior ray. -/
def wholeCutPiece (v : V) : Set Plane :=
  if root : v ∈ (A).roots then {x | ∃ t : ℝ, 0 ≤ t ∧ x = R.exits.ray (R.exitRoot ⟨v, root⟩) t}
  else segment ℝ (p v) (p ((A).parent v))

/-- This carrier keeps every terminal tail, including the part beyond the finite rim. -/
def wholeCarrier : Set Plane := ⋃ v, R.wholeCutPiece v

/-- The finite section of the complete carrier is exactly the previously prescribed forest. -/
theorem wholeCarrier_inter_sublevel {level : ℝ}
    (higher : ∀ v : V, (G).height (p v) < level) :
    R.wholeCarrier ∩ {x | (G).height x ≤ level} = (R.truncatedEmbedding level higher).carrier := by
  classical
  rw [R.truncatedEmbedding_carrier_eq level higher, wholeCarrier, Set.iUnion_inter]
  apply Set.iUnion_congr
  intro v
  by_cases root : v ∈ (A).roots
  · let r : {v // v ∈ (A).roots} := ⟨v, root⟩
    rw [wholeCutPiece, dif_pos root, R.cutLast_exit level r,
      R.exits.closed_ray_inter_sublevel (R.exitRoot r) (R.exit_origin_below level higher r),
      R.point_eq]
    rfl
  · rw [wholeCutPiece, dif_neg root, R.cutLast_interior_stem level root, Set.inter_eq_left]
    intro x hx
    have convex : Convex ℝ {x | (G).height x ≤ level} := by
      simpa using (G).convex_height.convex_le level
    exact convex.segment_subset (higher v).le (higher ((A).parent v)).le hx

open Classical in
/-- A finite named point determines the line of each complete cut. Rays use
the point at parameter one, independently of the artificial truncation. -/
def wholeCutSecond (v : V) : Plane :=
  if root : v ∈ (A).roots then R.exits.ray (R.exitRoot ⟨v, root⟩) 1 else p ((A).parent v)

local instance threeExitWholeVertexFintype : Fintype V := Fintype.ofFinite V

def wholeCutEquation (i : Fin (Fintype.card V)) : Plane →ᵃ[ℝ] ℝ :=
  let v := (Fintype.equivFin V).symm i
  segmentEquation (p v) (R.wholeCutSecond v)

theorem wholeCutEquation_ne_zero (i : Fin (Fintype.card V)) : R.wholeCutEquation i ≠ 0 :=
  segmentEquation_ne_zero _ _

theorem exit_ray_lineMap (r : {v // v ∈ (A).roots}) (t : ℝ) :
    R.exits.ray (R.exitRoot r) t =
      AffineMap.lineMap (p r.val) (R.exits.ray (R.exitRoot r) 1) t := by
  have eq : K.projectedVertex (R.exitRoot r).val = p r.val := rfl
  rw [SlopeEnvelope.ExteriorPlan.ray, SlopeEnvelope.ExteriorPlan.ray, R.point_eq, eq,
    one_smul, AffineMap.lineMap_apply_module', add_sub_cancel_left, add_comm]

theorem wholeCarrier_covered_by_equations {x : Plane} (member : x ∈ R.wholeCarrier) :
    ∃ i, R.wholeCutEquation i x = 0 := by
  classical
  obtain ⟨v, contains⟩ := Set.mem_iUnion.mp member
  refine ⟨Fintype.equivFin V v, ?_⟩
  simp only [wholeCutEquation, Equiv.symm_apply_apply]
  by_cases root : v ∈ (A).roots
  · let r : {v // v ∈ (A).roots} := ⟨v, root⟩
    rw [wholeCutPiece, dif_pos root] at contains
    obtain ⟨t, _, rfl⟩ := contains
    rw [wholeCutSecond, dif_pos root]
    rw [R.exit_ray_lineMap r t, AffineMap.apply_lineMap,
      segmentEquation_eq_zero (left_mem_segment ℝ _ _),
      segmentEquation_eq_zero (right_mem_segment ℝ _ _), AffineMap.lineMap_same]
    rfl
  · rw [wholeCutPiece, dif_neg root] at contains
    rw [wholeCutSecond, dif_neg root]
    exact segmentEquation_eq_zero contains

/-- The velocity of the actual terminal ray keeps the physical height change. -/
def physicalRayDirection (r : {v // v ∈ (A).roots}) : Space :=
  let root := R.exitRoot r
  let dir := R.exits.direction (R.exits.slope root)
  Cap.horizontalAtHeight dir (-(R.exits.rate root + inner ℝ dir B.reference))

theorem physicalRayDirection_ne_zero (r : {v // v ∈ (A).roots}) :
    R.physicalRayDirection r ≠ 0 := by
  intro zero
  have horizontal := congrArg Cap.horizontal zero
  simp only [physicalRayDirection, Cap.horizontal_horizontalAtHeight, map_zero] at horizontal
  have unit := R.exits.unit (R.exitRoot r)
  rw [horizontal, norm_zero] at unit
  norm_num at unit

/-- The terminal rays are literally straight on the physical roof. The
recentered height used for truncation affects no intrinsic velocities. -/
theorem physical_point_ray (M : (G₀).FiniteSlopeModel) (r : {v // v ∈ (A).roots})
    {t : ℝ} (time : 0 ≤ t) :
    SpatialEnvelope.point M.plane (R.exits.ray (R.exitRoot r) t) =
      SpatialEnvelope.point M.plane (R.exits.point (R.exitRoot r)) +
        t • R.physicalRayDirection r := by
  let root := R.exitRoot r
  let dir := R.exits.direction (R.exits.slope root)
  have recentered : (G).height (R.exits.ray root t) =
      (G).height (R.exits.point root) + t * R.exits.rate root := R.exits.height_ray root time
  rw [SlopeEnvelope.recenter_height, SlopeEnvelope.recenter_height] at recentered
  have reference : inner ℝ (R.exits.ray root t) B.reference =
      inner ℝ (R.exits.point root) B.reference + t * inner ℝ dir B.reference := by
    rw [SlopeEnvelope.ExteriorPlan.ray, inner_add_left, real_inner_smul_left]
  rw [reference] at recentered
  ext j
  fin_cases j
  · simp [SpatialEnvelope.point, SlopeEnvelope.ExteriorPlan.ray, physicalRayDirection,
      Cap.horizontalAtHeight, PiLp.add_apply, PiLp.smul_apply]
  · simp [SpatialEnvelope.point, SlopeEnvelope.ExteriorPlan.ray, physicalRayDirection,
      Cap.horizontalAtHeight, PiLp.add_apply, PiLp.smul_apply]
  · change SpatialEnvelope.point M.plane (R.exits.ray root t) 2 =
      (SpatialEnvelope.point M.plane (R.exits.point root) + t • R.physicalRayDirection r) 2
    rw [SpatialEnvelope.height_point, PiLp.add_apply, PiLp.smul_apply, SpatialEnvelope.height_point,
      physicalRayDirection, Cap.height_horizontalAtHeight, M.height_eq, M.height_eq]
    dsimp only [root, dir] at recentered ⊢
    simp only [smul_eq_mul]
    linarith only [recentered]

/-- A whole-space partition of the physical roof with its original cut lines marked. -/
structure WholeCutModel (M : (G₀).FiniteSlopeModel) where
  Index : Type
  finiteIndex : Fintype Index
  partition : SpatialEnvelope.WholePartition M.plane Index
  signs : Index → Fin (Fintype.card V) → Bool
  aligned : ∀ c x, x ∈ partition.footprint c → ∀ i,
    0 ≤ AffineArrangement.signed (R.wholeCutEquation i) (signs c i) x

attribute [instance] WholeCutModel.finiteIndex

/-- Align the actual unbounded roof to every prescribed seam and exterior ray. -/
def wholeCutModel (M : (G₀).FiniteSlopeModel) : R.WholeCutModel M :=
  Classical.choice (by
    obtain ⟨I, finite, P, signs, aligned⟩ := SpatialEnvelope.exists_wholePartition M.plane
      R.wholeCutEquation R.wholeCutEquation_ne_zero
    exact ⟨⟨I, finite, P, signs, aligned⟩⟩)

namespace WholeCutModel

variable {R}
  {M : (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel}
  (W : R.WholeCutModel M)

/-- Complete intrinsic cut metric of the actual component extension. -/
abbrev Cut := W.partition.Cut R.wholeCarrier

theorem complete : CompleteSpace W.Cut := W.partition.cut_complete R.wholeCarrier

theorem restore_surjective : Function.Surjective (W.partition.restoreCut R.wholeCarrier) :=
  W.partition.restoreCut_surjective R.wholeCarrier

theorem carrier_boundary : R.wholeCarrier ⊆ ⋃ i, frontier (W.partition.footprint i) := by
  intro x hx
  obtain ⟨i, zero⟩ := R.wholeCarrier_covered_by_equations hx
  have covered : x ∈ ⋃ j, W.partition.footprint j := W.partition.cover.symm ▸ Set.mem_univ x
  obtain ⟨j, member⟩ := Set.mem_iUnion.mp covered
  exact Set.mem_iUnion.mpr ⟨j, W.partition.mem_frontier_of_constraint R.wholeCutEquation
    R.wholeCutEquation_ne_zero W.signs W.aligned j member i zero⟩

end WholeCutModel
end Unfoldings.ConvexRoof.ThreeExitComponentRouting
