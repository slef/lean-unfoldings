module

public import Unfoldings.FewestNets.ThreeExitWholeCut
public import Unfoldings.Geometry.OrientedSubsegments

/-! The last fine link at the artificial rim belongs to one actual physical exit ray. -/

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
local notation "G" => SlopeEnvelope.recenter
  (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty) B.reference
local notation "p" => (fun v : V => K.projectedVertex (Subtype.val v))
local notation "Root" => {r : V // r ∈ R.stems.choice.parents.roots}

variable (level : ℝ)

/-- Any last oriented subsegment that reaches the artificial level lies
on a single actual exit and ends at its exact truncation parameter. -/
theorem exists_exit_of_subsegment_to_rim
    (higher : ∀ v : V, (G).height (p v) < level) {x y : Plane} (at_level : (G).height y = level)
    (P : (R.truncatedEmbedding level higher).OrientedSubsegment x y) :
    ∃ (r : Root) (t : ℝ), 0 ≤ t ∧ t < R.exits.timeAtLevel level (R.exitRoot r) ∧
      x = R.exits.ray (R.exitRoot r) t ∧ y = R.exits.pointAtLevel level (R.exitRoot r) := by
  have first := P.at_first
  have last := P.at_last
  change AffineMap.lineMap (R.truncatedPoint level P.edge.val)
    (R.truncatedPoint level (R.truncatedParents.parent P.edge.val)) P.first = x at first
  change AffineMap.lineMap (R.truncatedPoint level P.edge.val)
    (R.truncatedPoint level (R.truncatedParents.parent P.edge.val)) P.last = y at last
  have original : ∃ v : V, P.edge.val = .inl v := by
    rcases value : P.edge.val with v | r
    · exact ⟨v, rfl⟩
    · exact (P.edge.property ⟨r, value.symm⟩).elim
  obtain ⟨v, hv⟩ := original
  rw [hv] at first last
  change AffineMap.lineMap (p v) (R.cutLast level v) P.first = x at first
  change AffineMap.lineMap (p v) (R.cutLast level v) P.last = y at last
  have positive : 0 < P.last := P.first_mem.1.trans_lt P.increasing
  have final : P.last = 1 := by
    apply le_antisymm P.last_mem.2
    by_contra! before
    have open_seg : y ∈ openSegment ℝ (p v) (R.cutLast level v) := by
      rw [openSegment_eq_image_lineMap]
      exact ⟨P.last, ⟨positive, before⟩, last⟩
    exact (R.truncatedSegment_height_lt level higher v open_seg).ne at_level
  rw [final, AffineMap.lineMap_apply_one] at last
  have root : v ∈ R.stems.choice.parents.roots := by
    by_contra not_root
    rw [R.cutLast_interior_stem level not_root] at last
    exact (higher _).ne ((congrArg (G).height last).trans at_level)
  let r : Root := ⟨v, root⟩
  let τ := R.exits.timeAtLevel level (R.exitRoot r)
  have τ_pos : 0 < τ := R.exits.timeAtLevel_pos level _ (R.exit_origin_below level higher r)
  have first_lt : P.first < 1 := P.increasing.trans_le P.last_mem.2
  have tail : R.cutLast level v = R.exits.pointAtLevel level (R.exitRoot r) := R.cutLast_exit level r
  have parameter : x = R.exits.ray (R.exitRoot r) (P.first * τ) := by
    rw [tail] at first
    refine first.symm.trans ?_
    rw [SlopeEnvelope.ExteriorPlan.pointAtLevel,
      R.exit_ray_lineMap r τ, R.exit_ray_lineMap r (P.first * τ),
      AffineMap.lineMap_lineMap_right]
  exact ⟨r, P.first * τ, mul_nonneg P.first_mem.1 τ_pos.le,
    (mul_lt_mul_of_pos_right first_lt τ_pos).trans_eq (one_mul _), parameter, last.symm.trans tail⟩

end Unfoldings.ConvexRoof.ThreeExitComponentRouting
