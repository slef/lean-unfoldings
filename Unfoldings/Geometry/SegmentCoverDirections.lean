module

public import Unfoldings.Geometry.RadialSegment
public import Unfoldings.Geometry.AngleMonotone
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Data.Set.Finite.Lattice

/-! Whole-edge outward directions survive finite straight-segment meshing. -/

@[expose] public section

namespace Unfoldings

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine segment covered by finitely many sets shares two points with one fixed piece. -/
theorem exists_nontrivial_segment_inter [Finite I] {a b : E} (different : a ≠ b)
    (piece : I → Set E) (cover : segment ℝ a b ⊆ ⋃ i, piece i) :
    ∃ i, (segment ℝ a b ∩ piece i).Nontrivial := by
  have infinite_segment : (segment ℝ a b).Infinite := by
    rw [segment_eq_image_lineMap]
    exact (Set.Icc_infinite (show (0 : ℝ) < 1 from zero_lt_one)).image
      (AffineMap.lineMap_injective ℝ different).injOn
  by_contra none
  have finite_inter (i : I) : (segment ℝ a b ∩ piece i).Finite :=
    (Set.not_nontrivial_iff.mp (fun meeting => none ⟨i, meeting⟩)).finite
  apply infinite_segment
  apply (Set.finite_iUnion finite_inter).subset
  intro x member
  obtain ⟨i, in_piece⟩ := Set.mem_iUnion.mp (cover member)
  exact Set.mem_iUnion.mpr ⟨i, member, in_piece⟩

/-- On a positive-length overlap, two whole-edge outward orientations must agree. -/
theorem direction_pos_smul_of_outward_overlap (q a b u v : E)
    (old_outward : 0 ≤ inner ℝ (a - q) (b - a))
    (new_outward : 0 ≤ inner ℝ (u - q) (v - u)) (different : u ≠ v)
    {r s : ℝ} (nonnegative : 0 ≤ r) (ordered : r < s)
    (first : AffineMap.lineMap u v r ∈ segment ℝ a b)
    (last : AffineMap.lineMap u v s ∈ segment ℝ a b) :
    ∃ k : ℝ, 0 < k ∧ v - u = k • (b - a) := by
  obtain ⟨α, αbounds, at_first⟩ := (segment_eq_image_lineMap ℝ a b).subset first
  obtain ⟨β, βbounds, at_last⟩ := (segment_eq_image_lineMap ℝ a b).subset last
  have increasing := dist_lineMap_lt_of_inner_nonneg q u v new_outward different
    nonnegative ordered
  have old_order : α < β := by
    by_contra reversed
    have bound := dist_lineMap_le_of_inner_nonneg q a b old_outward βbounds.1
      (not_lt.mp reversed)
    rw [at_first, at_last] at bound
    exact (not_lt_of_ge bound) increasing
  have displacement : (β - α) • (b - a) = (s - r) • (v - u) := by
    calc
      _ = AffineMap.lineMap a b β - AffineMap.lineMap a b α := by
        simp only [AffineMap.lineMap_apply_module']
        module
      _ = AffineMap.lineMap u v s - AffineMap.lineMap u v r := by rw [at_first, at_last]
      _ = _ := by
        simp only [AffineMap.lineMap_apply_module']
        module
  refine ⟨(β - α) / (s - r), div_pos (sub_pos.mpr old_order) (sub_pos.mpr ordered), ?_⟩
  have scaled := congrArg (fun z : E => (s - r)⁻¹ • z) displacement
  simpa only [smul_smul, inv_mul_cancel₀ (sub_pos.mpr ordered).ne', one_smul,
    div_eq_inv_mul] using scaled.symm

/-- A whole outward meshed edge inherits the orientation of an actual supporting cut piece. -/
theorem exists_direction_pos_smul_of_segment_cover [Finite I] (q a b : E) (different : a ≠ b)
    (outward : 0 ≤ inner ℝ (a - q) (b - a)) (first last : I → E)
    (piece_outward : ∀ i, 0 ≤ inner ℝ (first i - q) (last i - first i))
    (cover : segment ℝ a b ⊆ ⋃ i, segment ℝ (first i) (last i)) :
    ∃ i, ∃ k : ℝ, 0 < k ∧ b - a = k • (last i - first i) := by
  obtain ⟨i, x, ⟨on_segment, on_piece⟩, y, ⟨last_segment, last_piece⟩, points_different⟩ :=
    exists_nontrivial_segment_inter different (fun i => segment ℝ (first i) (last i)) cover
  obtain ⟨r, rbounds, at_x⟩ := (segment_eq_image_lineMap ℝ a b).subset on_segment
  obtain ⟨s, sbounds, at_y⟩ := (segment_eq_image_lineMap ℝ a b).subset last_segment
  have parameters : r ≠ s := by
    intro equal
    exact points_different (at_x.symm.trans ((congrArg (AffineMap.lineMap a b) equal).trans at_y))
  rcases lt_or_gt_of_ne parameters with ordered | ordered
  · obtain ⟨k, positive, direction⟩ := direction_pos_smul_of_outward_overlap q (first i) (last i)
      a b (piece_outward i) outward different rbounds.1 ordered
      (at_x.symm ▸ on_piece) (at_y.symm ▸ last_piece)
    exact ⟨i, k, positive, direction⟩
  · obtain ⟨k, positive, direction⟩ := direction_pos_smul_of_outward_overlap q (first i) (last i)
      a b (piece_outward i) outward different sbounds.1 ordered
      (at_y.symm ▸ last_piece) (at_x.symm ▸ on_piece)
    exact ⟨i, k, positive, direction⟩

/-- Finite subdivision neither reverses the cuts nor widens their common direction wedge. -/
theorem direction_wedge_of_outward_segment_cover [Finite I] (q a b u v : E) (different : a ≠ b)
    (outward : 0 ≤ inner ℝ (a - q) (b - a)) (first last : I → E)
    (piece_outward : ∀ i, 0 ≤ inner ℝ (first i - q) (last i - first i))
    (cover : segment ℝ a b ⊆ ⋃ i, segment ℝ (first i) (last i))
    (directions : ∀ i, InDirectionWedge u v (last i - first i)) :
    InDirectionWedge u v (b - a) := by
  obtain ⟨i, k, positive, direction⟩ :=
    exists_direction_pos_smul_of_segment_cover q a b different outward first last
      piece_outward cover
  obtain ⟨r, s, rnonnegative, snonnegative, representation⟩ := directions i
  refine ⟨k * r, k * s, mul_nonneg positive.le rnonnegative,
    mul_nonneg positive.le snonnegative, ?_⟩
  rw [direction, representation, smul_add, smul_smul, smul_smul]

end Unfoldings
