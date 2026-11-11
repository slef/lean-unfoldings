module

public import Unfoldings.Geometry.ConvexRayBoundary
public import Mathlib.Tactic.Module

/-!
# Radial continuations of arbitrary seeds to a convex outer rim

The continuations from a common interior origin are disjoint or nested. Thus
adding skirt seeds introduces no transverse crossings. Seeds outside an inner
convex region have continuations outside that region's interior.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem segment_radial_eq_image (q r : E) {a : ℝ} (small : a ≤ 1) :
    segment ℝ (q + a • (r - q)) r =
      (fun t : ℝ => q + t • (r - q)) '' Set.Icc a 1 := by
  have image := image_segment ℝ (AffineMap.lineMap q r) a 1
  rw [segment_eq_Icc small, AffineMap.lineMap_apply_one] at image
  have function_eq : (fun t : ℝ => q + t • (r - q)) = AffineMap.lineMap q r := by
    funext t
    rw [AffineMap.lineMap_apply_module', add_comm]
  rw [function_eq]
  simpa only [AffineMap.lineMap_apply_module', add_comm] using image.symm

/-- Starting outside a convex region's interior and continuing outward cannot reenter it. -/
theorem radial_continuation_not_mem_interior {S : Set E} (convex : Convex ℝ S)
    {q p : E} (origin : q ∈ interior S) (outside : p ∉ interior S)
    {a : ℝ} (beyond : 1 ≤ a) : q + a • (p - q) ∉ interior S := by
  intro inside
  have positive : 0 < a := lt_of_lt_of_le zero_lt_one beyond
  have inverse : a⁻¹ ≤ 1 := (inv_le_one₀ positive).mpr beyond
  have member := convex.interior origin inside (sub_nonneg.mpr inverse)
    (inv_nonneg.mpr positive.le) (show (1 - a⁻¹) + a⁻¹ = 1 by ring)
  have expression : (1 - a⁻¹) • q + a⁻¹ • (q + a • (p - q)) = p := by
    simp only [smul_add, smul_smul, inv_mul_cancel₀ positive.ne', one_smul,
      sub_smul, smul_sub]
    abel
  exact outside (expression ▸ member)

structure RadialClipTail (S : Set E) (q p : E) where
  tip : E
  boundary : tip ∈ frontier S
  start : ℝ
  start_pos : 0 < start
  start_le : start ≤ 1
  seed_eq : p = q + start • (tip - q)

def radialClipTail {S : Set E} (compact : IsCompact S) (convex : Convex ℝ S)
    {q p : E} (origin : q ∈ interior S) (member : p ∈ S) (different : p ≠ q) :
    RadialClipTail S q p := Classical.choice (by
  obtain ⟨a, positive, boundary⟩ := exists_frontier_on_positive_ray compact convex origin different
  have beyond := one_le_frontier_ray_factor convex origin member positive boundary
  refine ⟨⟨q + a • (p - q), boundary, a⁻¹, inv_pos.mpr positive,
    (inv_le_one₀ positive).mpr beyond, ?_⟩⟩
  rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ positive.ne', one_smul, add_sub_cancel])

namespace RadialClipTail

variable {S : Set E} {q p r : E} (T : RadialClipTail S q p)

def carrier : Set E := segment ℝ p T.tip

theorem carrier_eq_image : T.carrier =
    (fun t : ℝ => q + t • (T.tip - q)) '' Set.Icc T.start 1 := by
  change segment ℝ p T.tip = _
  exact (congrArg (fun z : E => segment ℝ z T.tip) T.seed_eq).trans
    (segment_radial_eq_image q T.tip T.start_le)

theorem seed_mem : p ∈ T.carrier := left_mem_segment ℝ _ _

theorem tip_mem : T.tip ∈ T.carrier := right_mem_segment ℝ _ _

theorem subset (convex : Convex ℝ S) (closed : IsClosed S) (member : p ∈ S) :
    T.carrier ⊆ S := convex.segment_subset member (closed.frontier_subset T.boundary)

theorem carrier_not_mem_inner {B : Set E} (convex : Convex ℝ B)
    (origin : q ∈ interior B) (outside : p ∉ interior B) {x : E} (member : x ∈ T.carrier) :
    x ∉ interior B := by
  obtain ⟨a, bounds, rfl⟩ := T.carrier_eq_image.subset member
  have beyond : 1 ≤ a / T.start := (one_le_div T.start_pos).mpr bounds.1
  have expression : q + a • (T.tip - q) = q + (a / T.start) • (p - q) := by
    have vector := congrArg (fun z : E => z - q) T.seed_eq
    simp only [add_sub_cancel_left] at vector
    rw [vector, smul_smul, div_mul_cancel₀ _ T.start_pos.ne']
  change q + a • (T.tip - q) ∉ interior B
  rw [expression]
  exact radial_continuation_not_mem_interior convex origin outside beyond

/-- Intersecting continuations have the very same outer rim endpoint. -/
theorem tip_eq_of_intersection (convex : Convex ℝ S) (origin : q ∈ interior S)
    (U : RadialClipTail S q r) {x : E} (first : x ∈ T.carrier) (last : x ∈ U.carrier) :
    T.tip = U.tip := by
  obtain ⟨a, a_bounds, first_eq⟩ := T.carrier_eq_image.subset first
  obtain ⟨b, b_bounds, last_eq⟩ := U.carrier_eq_image.subset last
  exact frontier_eq_of_radial_rays_meet convex origin T.boundary U.boundary
    (T.start_pos.trans_le a_bounds.1) (U.start_pos.trans_le b_bounds.1)
    (first_eq.trans last_eq.symm)

/-- Two continuations are disjoint or one entire continuation is contained in the other. -/
theorem disjoint_or_nested (convex : Convex ℝ S) (origin : q ∈ interior S)
    (U : RadialClipTail S q r) :
    Disjoint T.carrier U.carrier ∨ T.carrier ⊆ U.carrier ∨ U.carrier ⊆ T.carrier := by
  by_cases disjoint : Disjoint T.carrier U.carrier
  · exact Or.inl disjoint
  · have meeting : ∃ x, x ∈ T.carrier ∧ x ∈ U.carrier := by
      by_contra absent
      exact disjoint (Set.disjoint_left.mpr (fun x first last => absent ⟨x, first, last⟩))
    obtain ⟨x, first, last⟩ := meeting
    have same := T.tip_eq_of_intersection convex origin U first last
    rw [T.carrier_eq_image, U.carrier_eq_image, same]
    rcases le_total T.start U.start with ordered | ordered
    · exact Or.inr (Or.inr (Set.image_mono (Set.Icc_subset_Icc_left ordered)))
    · exact Or.inr (Or.inl (Set.image_mono (Set.Icc_subset_Icc_left ordered)))

end RadialClipTail
end Unfoldings
