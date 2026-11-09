module

public import Unfoldings.Geometry.FrontierRays

/-!
# Continuous radial projection onto a bounded convex frontier

Gauge normalization gives an actual projection off the interior origin.
It fixes the frontier and is continuous away from the origin. This supports
local boundary arguments without a topological invariance-of-domain theorem.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

open Topology
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

omit [NormedSpace ℝ E] in
theorem frontier_vadd (v : E) (s : Set E) : frontier (v +ᵥ s) = v +ᵥ frontier s :=
  ((Homeomorph.vadd v).image_frontier s).symm

def frontierProjection (s : Set E) (x : E) : E := (gauge s x)⁻¹ • x

theorem frontierProjection_mem (convex : Convex ℝ s) (origin : (0 : E) ∈ interior s)
    (bounded : Bornology.IsBounded s) {x : E} (nonzero : x ≠ 0) :
    frontierProjection s x ∈ frontier s := by
  have neighborhood : s ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp origin
  have positive := (gauge_pos (absorbent_nhds_zero neighborhood)
    ((NormedSpace.isVonNBounded_iff ℝ).mpr bounded)).mpr nonzero
  apply (gauge_eq_one_iff_mem_frontier convex neighborhood).mp
  change gauge s ((gauge s x)⁻¹ • x) = 1
  rw [gauge_smul_of_nonneg (inv_nonneg.mpr positive.le)]
  exact inv_mul_cancel₀ positive.ne'

theorem frontierProjection_eq_self (convex : Convex ℝ s) (origin : (0 : E) ∈ interior s)
    {x : E} (boundary : x ∈ frontier s) : frontierProjection s x = x := by
  have height := (gauge_eq_one_iff_mem_frontier convex
    (mem_interior_iff_mem_nhds.mp origin)).mpr boundary
  simp only [frontierProjection, height, inv_one, one_smul]

theorem continuousAt_frontierProjection (convex : Convex ℝ s) (origin : (0 : E) ∈ interior s)
    (bounded : Bornology.IsBounded s) {x : E} (nonzero : x ≠ 0) :
    ContinuousAt (frontierProjection s) x := by
  have neighborhood : s ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp origin
  have positive := (gauge_pos (absorbent_nhds_zero neighborhood)
    ((NormedSpace.isVonNBounded_iff ℝ).mpr bounded)).mpr nonzero
  exact ((continuous_gauge convex neighborhood).continuousAt.inv₀ positive.ne').smul
    continuousAt_id

def frontierProjectionFrom (s : Set E) (origin x : E) : E :=
  frontierProjection (-origin +ᵥ s) (x - origin) + origin

theorem frontierProjectionFrom_mem (convex : Convex ℝ s) (compact : IsCompact s)
    {origin x : E} (inside : origin ∈ interior s) (different : x ≠ origin) :
    frontierProjectionFrom s origin x ∈ frontier s := by
  have zero_inside : (0 : E) ∈ interior (-origin +ᵥ s) := by
    rw [interior_vadd]
    exact ⟨origin, inside, by simp⟩
  have compact_shift : IsCompact (-origin +ᵥ s) := by
    change IsCompact ((fun y : E => -origin + y) '' s)
    exact compact.image (continuous_const.add continuous_id)
  have member := frontierProjection_mem (convex.vadd (-origin)) zero_inside
    compact_shift.isBounded (sub_ne_zero.mpr different)
  rw [frontier_vadd] at member
  obtain ⟨y, hy, equal⟩ := member
  change frontierProjection (-origin +ᵥ s) (x - origin) + origin ∈ frontier s
  have recovered : frontierProjection (-origin +ᵥ s) (x - origin) + origin = y := by
    rw [← equal]
    change (-origin + y) + origin = y
    abel
  rwa [recovered]

theorem frontierProjectionFrom_eq_self (convex : Convex ℝ s)
    {origin x : E} (inside : origin ∈ interior s) (boundary : x ∈ frontier s) :
    frontierProjectionFrom s origin x = x := by
  have zero_inside : (0 : E) ∈ interior (-origin +ᵥ s) := by
    rw [interior_vadd]
    exact ⟨origin, inside, by simp⟩
  have shifted : x - origin ∈ frontier (-origin +ᵥ s) := by
    rw [frontier_vadd]
    exact ⟨x, boundary, by change -origin + x = x - origin; abel⟩
  rw [frontierProjectionFrom,
    frontierProjection_eq_self (convex.vadd (-origin)) zero_inside shifted, sub_add_cancel]

theorem continuousAt_frontierProjectionFrom (convex : Convex ℝ s) (compact : IsCompact s)
    {origin x : E} (inside : origin ∈ interior s) (different : x ≠ origin) :
    ContinuousAt (frontierProjectionFrom s origin) x := by
  have zero_inside : (0 : E) ∈ interior (-origin +ᵥ s) := by
    rw [interior_vadd]
    exact ⟨origin, inside, by simp⟩
  have compact_shift : IsCompact (-origin +ᵥ s) := by
    change IsCompact ((fun y : E => -origin + y) '' s)
    exact compact.image (continuous_const.add continuous_id)
  have projection := continuousAt_frontierProjection (convex.vadd (-origin)) zero_inside
    compact_shift.isBounded (sub_ne_zero.mpr different)
  exact (projection.comp (f := fun y : E => y - origin) (x := x)
    (continuousAt_id.sub continuousAt_const)).add continuousAt_const

theorem frontierProjectionFrom_eq_of_level (origin x : E) (f : E →L[ℝ] ℝ) (a : ℝ)
    (below : f origin < a) (level : f x = a)
    (projected_level : f (frontierProjectionFrom s origin x) = a) :
    frontierProjectionFrom s origin x = x := by
  let r := (gauge (-origin +ᵥ s) (x - origin))⁻¹
  change f (r • (x - origin) + origin) = a at projected_level
  rw [map_add, map_smul, map_sub, level] at projected_level
  change r * (a - f origin) + f origin = a at projected_level
  have parameter : r = 1 := by nlinarith
  change r • (x - origin) + origin = x
  rw [parameter, one_smul, sub_add_cancel]

end Unfoldings
