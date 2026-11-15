module

public import Unfoldings.Geometry.HingeCircleContinuity
public import Unfoldings.Topology.ProperClosedGraph

/-! Jointly continuous source-circle contacts throughout an actual outward hinge sweep. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (hinge : Fin (n + 1)) (nonzero : R.direction ≠ 0)
  (angle : ℝ) (radial : ∀ θ ∈ Set.Icc 0 angle, (R.rotateSuffix hinge θ).Outward)

/-- Vary both the opening angle and the original-source radius, retaining the actual bank. -/
def hingeSweepPoint (p : Set.Icc 0 angle × ℝ≥0) : ℂ :=
  R.hingeCirclePoint hinge nonzero angle radial p.2 p.1

include nonzero radial in
/-- Whole-bank membership is closed jointly, including the prefix that remains fixed. -/
theorem hingeSweepPoint_graph_closed :
    IsClosed (R.hingeSweepPoint hinge nonzero angle radial).graph := by
  let back : (Set.Icc 0 angle × ℝ≥0) × ℂ → ℂ := fun p =>
    R.chain.vertex hinge + complexRotation (-p.1.1.val) (p.2 - R.chain.vertex hinge)
  have continuous_back : Continuous back := by
    dsimp only [back, complexRotation_apply, polarRay]
    fun_prop
  have prefix_closed : IsClosed (Set.range
      (R.chain.interval 0 hinge.val (by omega)).path) :=
    (isCompact_range (R.chain.interval 0 hinge.val (by omega)).path.continuous).isClosed
  have carrier_closed : IsClosed {p : (Set.Icc 0 angle × ℝ≥0) × ℂ |
      p.2 ∈ Set.range (R.chain.interval 0 hinge.val (by omega)).path ∨
      back p ∈ (R.suffix hinge).carrier} :=
    (prefix_closed.preimage continuous_snd).union
      (((R.suffix hinge).isClosed_carrier nonzero).preimage continuous_back)
  have radius_closed : IsClosed {p : (Set.Icc 0 angle × ℝ≥0) × ℂ |
      dist R.start p.2 = (p.1.2 : ℝ)} := isClosed_eq (by fun_prop) (by fun_prop)
  have equal : (R.hingeSweepPoint hinge nonzero angle radial).graph =
      {p : (Set.Icc 0 angle × ℝ≥0) × ℂ | dist R.start p.2 = (p.1.2 : ℝ)} ∩
        {p | p.2 ∈ Set.range (R.chain.interval 0 hinge.val (by omega)).path ∨
          back p ∈ (R.suffix hinge).carrier} := by
    ext p
    rcases p with ⟨⟨θ, r⟩, z⟩
    change R.hingeCirclePoint hinge nonzero angle radial r θ = z ↔
      dist R.start z = (r : ℝ) ∧
        (z ∈ Set.range (R.chain.interval 0 hinge.val (by omega)).path ∨
          back ((θ, r), z) ∈ (R.suffix hinge).carrier)
    have carrier : z ∈ (R.rotateSuffix hinge θ.val).carrier ↔
        z ∈ Set.range (R.chain.interval 0 hinge.val (by omega)).path ∨
          back ((θ, r), z) ∈ (R.suffix hinge).carrier := by
      rw [(R.rotateSuffix hinge θ.val).carrier_split hinge,
        R.rotateSuffix_prefix, R.rotateSuffix_suffix_carrier, Set.mem_union,
        (R.suffix hinge).mem_rotatedCarrier_iff_rotate_back]
      rfl
    constructor
    · rintro rfl
      refine ⟨R.hingeCirclePoint_radius hinge nonzero angle radial r θ, ?_⟩
      exact carrier.mp ((R.rotateSuffix hinge θ.val).radialPoint_mem
        (radial θ.val θ.property) (R.rotateSuffix_direction_ne_zero hinge θ.val nonzero) r)
    · rintro ⟨radius, member⟩
      apply (R.rotateSuffix hinge θ.val).eq_of_radius_eq (radial θ.val θ.property)
        (R.rotateSuffix_direction_ne_zero hinge θ.val nonzero)
        ((R.rotateSuffix hinge θ.val).radialPoint_mem (radial θ.val θ.property)
          (R.rotateSuffix_direction_ne_zero hinge θ.val nonzero) r) (carrier.mpr member)
      rw [R.rotateSuffix_start]
      change dist R.start (R.hingeCirclePoint hinge nonzero angle radial r θ) = dist R.start z
      exact (R.hingeCirclePoint_radius hinge nonzero angle radial r θ).trans radius.symm
  rw [equal]
  exact radius_closed.inter carrier_closed

include nonzero radial in
/-- Joint continuity holds even below the hinge circle and at the common source. -/
theorem continuous_hingeSweepPoint :
    Continuous (R.hingeSweepPoint hinge nonzero angle radial) := by
  apply continuous_of_isClosed_graph_of_proper_comp
    (R.hingeSweepPoint_graph_closed hinge nonzero angle radial) (dist R.start)
    (isProperMap_dist R.start)
  have equal : (dist R.start) ∘ R.hingeSweepPoint hinge nonzero angle radial =
      fun p : Set.Icc 0 angle × ℝ≥0 => (p.2 : ℝ) := by
    funext p
    exact R.hingeCirclePoint_radius hinge nonzero angle radial p.2 p.1
  rw [equal]
  fun_prop

end Unfoldings.PolygonalRay
