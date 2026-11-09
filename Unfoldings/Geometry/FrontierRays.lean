module

public import Unfoldings.Geometry.ConvexBoundaryRays
public import Mathlib.Analysis.Convex.Gauge

/-!
# Positive radial hulls of a bounded convex frontier

Mathlib's gauge normalizes every nonzero direction to the actual frontier.
Uniqueness on rays then lifts disjoint frontier subsets to disjoint positive
radial hulls. These statements do not depend on polyhedral geometry.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

open Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def positiveRadialHull (s : Set E) : Set E :=
  {z | ∃ r : ℝ, 0 < r ∧ ∃ y ∈ s, z = r • y}

theorem positiveRadialHull_mono {s t : Set E} (included : s ⊆ t) :
    positiveRadialHull s ⊆ positiveRadialHull t := by
  rintro z ⟨r, positive, y, member, equal⟩
  exact ⟨r, positive, y, included member, equal⟩

theorem positiveRadialHull_iUnion {ι : Sort*} (s : ι → Set E) :
    positiveRadialHull (⋃ i, s i) = ⋃ i, positiveRadialHull (s i) := by
  ext z
  constructor
  · rintro ⟨r, positive, y, member, equal⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
    exact Set.mem_iUnion.mpr ⟨i, r, positive, y, hi, equal⟩
  · intro member
    obtain ⟨i, r, positive, y, hy, equal⟩ := Set.mem_iUnion.mp member
    exact ⟨r, positive, y, Set.mem_iUnion.mpr ⟨i, hy⟩, equal⟩

theorem positiveRadialHull_openSegment (x y : E) :
    positiveRadialHull (openSegment ℝ x y) =
      {z | ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, 0 < b ∧ z = a • x + b • y} := by
  ext z
  constructor
  · rintro ⟨r, positive, p, ⟨a, b, ha, hb, _sum, combination⟩, equal⟩
    refine ⟨r * a, mul_pos positive ha, r * b, mul_pos positive hb, ?_⟩
    rw [equal, ← combination, smul_add, smul_smul, smul_smul]
  · rintro ⟨a, ha, b, hb, equal⟩
    have positive : 0 < a + b := add_pos ha hb
    refine ⟨a + b, positive, (a / (a + b)) • x + (b / (a + b)) • y,
      ⟨a / (a + b), b / (a + b), div_pos ha positive, div_pos hb positive, ?_, rfl⟩, ?_⟩
    · rw [← add_div, div_self positive.ne']
    · rw [smul_add, smul_smul, smul_smul,
        mul_div_cancel₀ _ positive.ne', mul_div_cancel₀ _ positive.ne']
      exact equal

theorem exists_frontier_positive_smul {s : Set E} (convex : Convex ℝ s)
    (origin : (0 : E) ∈ interior s) (bounded : Bornology.IsBounded s)
    {z : E} (nonzero : z ≠ 0) : ∃ r : ℝ, 0 < r ∧ r • z ∈ frontier s := by
  have neighborhood : s ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp origin
  have positive := (gauge_pos (absorbent_nhds_zero neighborhood)
    ((NormedSpace.isVonNBounded_iff ℝ).mpr bounded)).mpr nonzero
  refine ⟨(gauge s z)⁻¹, inv_pos.mpr positive, ?_⟩
  apply (gauge_eq_one_iff_mem_frontier convex neighborhood).mp
  rw [gauge_smul_of_nonneg (inv_nonneg.mpr positive.le)]
  exact inv_mul_cancel₀ positive.ne'

theorem positiveRadialHull_frontier {s : Set E} (convex : Convex ℝ s)
    (origin : (0 : E) ∈ interior s) (bounded : Bornology.IsBounded s) :
    positiveRadialHull (frontier s) = ({0} : Set E)ᶜ := by
  ext z
  constructor
  · rintro ⟨r, positive, y, boundary, equal⟩
    change z ≠ 0
    intro zero
    have y_zero : y = 0 := (smul_eq_zero.mp (equal.symm.trans zero)).resolve_left positive.ne'
    exact boundary.2 (y_zero ▸ origin)
  · intro outside
    obtain ⟨r, positive, boundary⟩ := exists_frontier_positive_smul convex origin bounded outside
    refine ⟨r⁻¹, inv_pos.mpr positive, r • z, boundary, ?_⟩
    rw [smul_smul, inv_mul_cancel₀ positive.ne', one_smul]

theorem disjoint_positiveRadialHulls_of_frontier {s a b : Set E} (convex : Convex ℝ s)
    (origin : (0 : E) ∈ interior s) (ha : a ⊆ frontier s) (hb : b ⊆ frontier s)
    (apart : Disjoint a b) : Disjoint (positiveRadialHull a) (positiveRadialHull b) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨r, rpos, x, hx, zx⟩ ⟨t, tpos, y, hy, zy⟩
  have ray : y = (r / t) • x := by
    calc
      y = t⁻¹ • (t • y) := by rw [smul_smul, inv_mul_cancel₀ tpos.ne', one_smul]
      _ = t⁻¹ • (r • x) := by rw [← zy, zx]
      _ = _ := by rw [smul_smul, div_eq_mul_inv, mul_comm]
  have same := eq_of_frontier_eq_nonnegative_smul convex origin (ha hx) (hb hy)
    (div_nonneg rpos.le tpos.le) ray
  exact Set.disjoint_left.mp apart hx (same ▸ hy)

end Unfoldings
