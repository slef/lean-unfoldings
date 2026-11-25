module

public import Unfoldings.FewestNets.ThreeExitOriginalFaceLift
public import Unfoldings.Geometry.SpatialEnvelopeRayGerms
public import Unfoldings.Convex.ExteriorBankSupports

/-! Every positive exit point has the exact single-cut, two-halfplane physical model. -/

@[expose] public section

noncomputable section

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
local notation "Root" => {r : V // r ∈ R.stems.choice.parents.roots}
local notation "p" => (fun v : V => K.projectedVertex (Subtype.val v))
local notation "q" => (fun (r : Root) => R.exits.ray (R.exitRoot r) 1)

theorem exit_endpoints_ne (r : Root) : p r.val ≠ q r := by
  have origin : R.exits.point (R.exitRoot r) = p r.val := R.point_eq _
  rw [← origin]
  exact R.exits.ray_endpoints_ne (R.exitRoot r)

private theorem wholeCutPiece_open_or_vertex (v : V) {x : Plane}
    (member : x ∈ R.wholeCutPiece v) : x ∈ R.openPiece v ∨ ∃ w : V, x = p w := by
  classical
  by_cases root : v ∈ (A).roots
  · rw [wholeCutPiece, dif_pos root] at member
    obtain ⟨t, nonnegative, rfl⟩ := member
    rcases eq_or_lt_of_le nonnegative with zero | positive
    · exact Or.inr ⟨v, by
        rw [← zero, SlopeEnvelope.ExteriorPlan.ray, zero_smul, add_zero, R.point_eq]
        rfl⟩
    · rw [R.openPiece_root ⟨v, root⟩]
      exact Or.inl ⟨t, positive, rfl⟩
  · rw [wholeCutPiece, dif_neg root] at member
    by_cases source : x = p v
    · exact Or.inr ⟨v, source⟩
    by_cases parent : x = p ((A).parent v)
    · exact Or.inr ⟨(A).parent v, parent⟩
    rw [R.openPiece_stem root]
    exact Or.inl (mem_openSegment_of_ne_left_right (Ne.symm source) (Ne.symm parent) member)

/-- The full cut and the one-ray cut have identical germs along the open exit. -/
theorem exists_exit_rayCut_germ (r : Root) {t : ℝ} (positive : 0 < t) :
    ∃ δ > 0, ∀ z, dist z (R.exits.ray (R.exitRoot r) t) < δ →
      (z ∈ R.wholeCarrier ↔ z ∈ MetricGluing.rayCut (p r.val) (q r)) := by
  classical
  let x := R.exits.ray (R.exitRoot r) t
  have open_x : x ∈ R.openPiece r.val := by
    rw [R.openPiece_root r]
    exact ⟨t, positive, rfl⟩
  let others := ⋃ v : {v : V // v ≠ r.val}, R.wholeCutPiece v.val
  have closed_others : IsClosed others := isClosed_iUnion_of_finite
    (fun v => R.isClosed_wholeCutPiece v.val)
  have outside : x ∈ othersᶜ := by
    intro member
    obtain ⟨v, inside⟩ := Set.mem_iUnion.mp member
    rcases R.wholeCutPiece_open_or_vertex v.val inside with on_open | ⟨w, at_vertex⟩
    · exact Set.disjoint_left.mp (R.openPieces_pairwise_disjoint v.property.symm) open_x on_open
    · exact R.openPiece_avoids_original_vertices r.val w (at_vertex ▸ open_x)
  obtain ⟨δ, δpos, isolated⟩ := Metric.isOpen_iff.mp closed_others.isOpen_compl x outside
  refine ⟨δ, δpos, ?_⟩
  intro z close
  constructor
  · intro member
    obtain ⟨v, on_piece⟩ := Set.mem_iUnion.mp member
    have same : v = r.val := by
      by_contra different
      exact isolated (Metric.mem_ball.mpr close) (Set.mem_iUnion.mpr ⟨⟨v, different⟩, on_piece⟩)
    subst v
    rwa [R.wholeCutPiece_root_eq_rayCut r] at on_piece
  · intro member
    exact Set.mem_iUnion.mpr ⟨r.val, (R.wholeCutPiece_root_eq_rayCut r).symm ▸ member⟩

/-- The actual complete cut near any positive terminal point is just its
oriented support line. All other pieces miss a full open ball. -/
theorem exists_exit_cut_line_germ (r : Root) {t : ℝ} (positive : 0 < t) :
    ∃ δ > 0, ∀ z, dist z (R.exits.ray (R.exitRoot r) t) < δ →
      (z ∈ R.wholeCarrier ↔ orientMap (p r.val) (q r) z = 0) := by
  let x := R.exits.ray (R.exitRoot r) t
  obtain ⟨δ, δpos, isolated⟩ := R.exists_exit_rayCut_germ r positive
  have forward : x ∈ rayForwardHalfspace (p r.val) (q r) := by
    dsimp only [x]
    rw [R.exit_ray_lineMap r t]
    exact lineMap_mem_rayForwardHalfspace (R.exit_endpoints_ne r) positive
  obtain ⟨ε, εpos, forward_ball⟩ :=
    Metric.isOpen_iff.mp (isOpen_rayForwardHalfspace (p r.val) (q r)) x forward
  refine ⟨min δ ε, lt_min δpos εpos, ?_⟩
  intro z close
  rw [isolated z (close.trans_le (min_le_left δ ε))]
  constructor
  · exact MetricGluing.rayCut_on_line _ _ z
  · intro zero
    obtain ⟨s, spos, expression⟩ := exists_positive_ray_parameter
      (R.exit_endpoints_ne r) (forward_ball (Metric.mem_ball.mpr (close.trans_le (min_le_right δ ε))))
      zero
    exact ⟨⟨s, spos.le⟩, expression.symm⟩

local instance terminalVertexFintype : Fintype V := Fintype.ofFinite _

namespace WholeCutModel

variable {R}
  {M : (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel}
  (W : R.WholeCutModel M)

/-- The whole partition retains the signed cells of this exact exit line. -/
def exitSigns (r : Root) (c : W.Index) : Bool :=
  W.signs c (Fintype.equivFin V r.val)

theorem exit_aligned (r : Root) (c : W.Index) (x : Plane) (member : x ∈ W.partition.footprint c) :
    0 ≤ AffineArrangement.signed (orientMap (p r.val) (q r)) (W.exitSigns r c) x := by
  classical
  have h := W.aligned c x member (Fintype.equivFin V r.val)
  simpa [exitSigns, wholeCutEquation, wholeCutSecond, r.property, segmentEquation,
    R.exit_endpoints_ne r] using h

private theorem exit_height_affine (r : Root) (t : ℝ) (nonnegative : 0 ≤ t) :
    SpatialEnvelope.height M.plane (AffineMap.lineMap (p r.val) (q r) t) =
      AffineMap.lineMap (SpatialEnvelope.height M.plane (p r.val))
        (SpatialEnvelope.height M.plane (q r)) t := by
  let root := R.exitRoot r
  have source : R.exits.point root = p r.val := R.point_eq _
  have height_at (s : ℝ) (hs : 0 ≤ s) :
      SpatialEnvelope.height M.plane (R.exits.ray root s) =
        SpatialEnvelope.height M.plane (p r.val) + s * R.physicalRayDirection r 2 := by
    have spatial := congrArg (fun X : Space => X 2) (R.physical_point_ray M r hs)
    simpa only [root, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, SpatialEnvelope.height_point,
      source] using spatial
  rw [← R.exit_ray_lineMap r t, height_at t nonnegative, AffineMap.lineMap_apply_ring',
    height_at 1 zero_le_one]
  ring

/-- Choose two actual cells that give the left and right rigid roof charts
on the whole positive exit. The chart neighborhoods see no other cut. -/
theorem exists_exit_local_model (r : Root) :
    ∃ (anchor : Bool → W.Index) (T : ℝ), 0 < T ∧ (∀ side, W.exitSigns r (anchor side) = side) ∧
      (∀ side t, T ≤ t → R.exits.ray (R.exitRoot r) t ∈ W.partition.footprint (anchor side)) ∧
      (∀ side t, 0 ≤ t → SpatialEnvelope.height M.plane (R.exits.ray (R.exitRoot r) t) =
        (M.plane (W.partition.support (anchor side))).height (R.exits.ray (R.exitRoot r) t)) ∧
      ∀ side t, 0 < t → ∃ δ > 0, ∀ z, dist z (R.exits.ray (R.exitRoot r) t) < δ →
        (z ∈ R.wholeCarrier ↔ orientMap (p r.val) (q r) z = 0) ∧
        (0 ≤ AffineArrangement.signed (orientMap (p r.val) (q r)) side z →
          SpatialEnvelope.height M.plane z = (M.plane (W.partition.support (anchor side))).height z) := by
  obtain ⟨anchor, T, positive, sign_eq, terminal, active, face⟩ :=
    W.partition.exists_straightRay_support_cells (R.exit_endpoints_ne r) (W.exitSigns r)
      (W.exit_aligned r) (exit_height_affine (M := M) r)
  refine ⟨anchor, T, positive, sign_eq, ?_, ?_, ?_⟩
  · intro side t after
    rw [R.exit_ray_lineMap r t]
    exact terminal side t after
  · intro side t nonnegative
    rw [R.exit_ray_lineMap r t]
    exact active side t nonnegative
  · intro side t positive
    obtain ⟨δ, δ_pos, cut⟩ := R.exists_exit_cut_line_germ r positive
    obtain ⟨ε, ε_pos, half⟩ := face side t positive
    refine ⟨min δ ε, lt_min δ_pos ε_pos, ?_⟩
    intro z near
    refine ⟨cut z (near.trans_le (min_le_left δ ε)), ?_⟩
    apply half z
    rw [← R.exit_ray_lineMap r t]
    exact near.trans_le (min_le_right δ ε)

end WholeCutModel
end Unfoldings.ConvexRoof.ThreeExitComponentRouting
