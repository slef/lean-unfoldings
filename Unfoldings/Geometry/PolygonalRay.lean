module

public import Unfoldings.Geometry.ChainPaths
public import Unfoldings.Geometry.RadialChain
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Topology.Order.IntermediateValue

/-! Polygonal rays retain their finite bends and an actual unbounded straight tail. -/

@[expose] public section

noncomputable section

open Topology
open scoped NNReal

namespace Unfoldings

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n : ℕ)

/-- No embedding or nonoverlap is built into the representation. -/
structure PolygonalRay where
  chain : PolygonalChain E n
  direction : E

namespace PolygonalRay

variable {E n} (R : PolygonalRay E n)

def start : E := R.chain.vertex 0

def tail (t : ℝ≥0) : E := R.chain.vertex (Fin.last n) + (t : ℝ) • R.direction

def carrier : Set E := Set.range R.chain.path ∪ Set.range R.tail

@[simp] theorem tail_zero : R.tail 0 = R.chain.vertex (Fin.last n) := by
  simp [tail]

theorem start_mem : R.start ∈ R.carrier :=
  Or.inl ⟨0, R.chain.path.source⟩

theorem tail_mem (t : ℝ≥0) : R.tail t ∈ R.carrier := Or.inr ⟨t, rfl⟩

theorem continuous_tail : Continuous R.tail := by
  unfold tail
  fun_prop

/-- The actual eventual straight ray is closed, without a boundedness assumption. -/
theorem isClosed_range_tail (nonzero : R.direction ≠ 0) : IsClosed (Set.range R.tail) := by
  have line : IsClosedEmbedding (fun t : ℝ =>
      R.chain.vertex (Fin.last n) + t • R.direction) :=
    (Homeomorph.addLeft (R.chain.vertex (Fin.last n))).isClosedEmbedding.comp
      (isClosedEmbedding_smul_left nonzero)
  exact (line.comp NNReal.isClosedEmbedding_coe).isClosed_range

theorem isClosed_carrier (nonzero : R.direction ≠ 0) : IsClosed R.carrier :=
  (isCompact_range R.chain.path.continuous).isClosed.union (R.isClosed_range_tail nonzero)

/-- Source-radial monotonicity is tested on all finite edges and the true tail. -/
def Outward : Prop :=
  R.chain.RadialFrom R.start 0 ∧
    0 ≤ inner ℝ (R.chain.vertex (Fin.last n) - R.start) R.direction

theorem tail_lineMap (t : ℝ≥0) : R.tail t =
    AffineMap.lineMap (R.chain.vertex (Fin.last n))
      (R.chain.vertex (Fin.last n) + R.direction) (t : ℝ) := by
  simp [tail, AffineMap.lineMap_apply_module', add_comm]

/-- A nonconstant outward tail crosses each source-centered circle at most once. -/
theorem tail_radius_strictMono (outward : R.Outward) (nonzero : R.direction ≠ 0) :
    StrictMono (fun t => dist R.start (R.tail t)) := by
  intro t s ordered
  change dist R.start (R.tail t) < dist R.start (R.tail s)
  rw [R.tail_lineMap, R.tail_lineMap]
  apply dist_lineMap_lt_of_inner_nonneg
  · simpa only [add_sub_cancel_left] using outward.2
  · simpa only [ne_eq, left_eq_add] using nonzero
  · exact t.coe_nonneg
  · exact ordered

/-- Any radius can be reached at or beyond the tail's initial radius. -/
theorem exists_tail_radius_ge (nonzero : R.direction ≠ 0) (r : ℝ) :
    ∃ t : ℝ≥0, r ≤ dist R.start (R.tail t) := by
  let d := dist R.start (R.chain.vertex (Fin.last n))
  let t : ℝ≥0 := NNReal.mk ((max r 0 + d) / ‖R.direction‖)
    (div_nonneg (add_nonneg (le_max_right _ _) dist_nonneg) (norm_nonneg _))
  have positive : 0 < ‖R.direction‖ := norm_pos_iff.mpr nonzero
  have length : dist (R.chain.vertex (Fin.last n)) (R.tail t) = max r 0 + d := by
    rw [tail, dist_self_add_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.coe_nonneg]
    exact div_mul_cancel₀ _ positive.ne'
  have triangle := dist_triangle (R.chain.vertex (Fin.last n)) R.start (R.tail t)
  rw [length, dist_comm (R.chain.vertex (Fin.last n)) R.start] at triangle
  change max r 0 + d ≤ d + dist R.start (R.tail t) at triangle
  refine ⟨t, ?_⟩
  linarith only [triangle, le_max_left r 0]

end PolygonalRay
end Unfoldings
