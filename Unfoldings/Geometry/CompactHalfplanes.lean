module

public import Unfoldings.Geometry.CompactCollinear
public import Unfoldings.Geometry.SegmentVertices
public import Unfoldings.Geometry.ConvexSegmentExit

/-! Compact finite affine halfplane intersections have exact finite segment rims. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {ι : Type*} [Finite ι] (equation : ι → Plane →ᵃ[ℝ] ℝ)
  (proper : ∀ i, equation i ≠ 0)

def nonpositiveRegion : Set Plane := {x | ∀ i, equation i x ≤ 0}

omit [Finite ι] in
theorem isClosed_nonpositiveRegion : IsClosed (nonpositiveRegion equation) := by
  have equal : nonpositiveRegion equation = ⋂ i, (equation i) ⁻¹' Set.Iic 0 := by
    ext x
    simp only [nonpositiveRegion, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Iic]
  rw [equal]
  exact isClosed_iInter (fun i =>
    isClosed_Iic.preimage (equation i).continuous_of_finiteDimensional)

omit [Finite ι] in
theorem convex_nonpositiveRegion : Convex ℝ (nonpositiveRegion equation) := by
  have equal : nonpositiveRegion equation = ⋂ i, (equation i) ⁻¹' Set.Iic 0 := by
    ext x
    simp only [nonpositiveRegion, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Iic]
  rw [equal]
  exact convex_iInter (fun i => (convex_Iic (0 : ℝ)).affine_preimage (equation i))

theorem nonpositiveRegion_frontier_support {x : Plane}
    (boundary : x ∈ frontier (nonpositiveRegion equation)) : ∃ i, equation i x = 0 := by
  classical
  have member : x ∈ nonpositiveRegion equation :=
    (isClosed_nonpositiveRegion equation).frontier_subset boundary
  by_contra nonzero
  let U := ⋂ i, (equation i) ⁻¹' Set.Iio 0
  have opens : IsOpen U := isOpen_iInter_of_finite
    (fun i => isOpen_Iio.preimage (equation i).continuous_of_finiteDimensional)
  have inside : x ∈ U := Set.mem_iInter.mpr (fun i => lt_of_le_of_ne (member i)
    (fun zero => nonzero ⟨i, zero⟩))
  have subset : U ⊆ nonpositiveRegion equation := by
    intro p inside i
    exact ((Set.mem_iInter.mp inside) i).le
  have in_interior : x ∈ interior U := by rwa [opens.interior_eq]
  exact boundary.2 (interior_mono subset in_interior)

include proper in
/-- Every compact finite affine halfplane intersection has an exact finite segment boundary. -/
theorem exists_finite_nonpositive_boundary_segments
    (compact : IsCompact (nonpositiveRegion equation)) :
    ∃ edges : Set (Plane × Plane), edges.Finite ∧
      frontier (nonpositiveRegion equation) = segmentCarrier edges := by
  classical
  let := Fintype.ofFinite ι
  let rim (i : ι) := nonpositiveRegion equation ∩ {x | equation i x = 0}
  have rim_boundary (i : ι) : rim i ⊆ frontier (nonpositiveRegion equation) := by
    intro x member
    refine ⟨subset_closure member.1, ?_⟩
    intro interior_point
    have vanishes_open : equation i = 0 := by
      apply AffineMap.ext_on (isOpen_interior.affineSpan_eq_top ⟨x, interior_point⟩)
      intro p hp
      have zero_at_x := member.2
      have lower : equation i p ≤ 0 := (interior_subset hp) i
      change equation i p = 0
      by_contra unequal
      have negative : equation i p < 0 := lt_of_le_of_ne lower unequal
      obtain ⟨a, after, in_region⟩ := exists_lineMap_beyond_one_mem (q := p) interior_point
      have bound := in_region i
      rw [(equation i).apply_lineMap, AffineMap.lineMap_apply_ring, zero_at_x] at bound
      nlinarith [mul_pos (sub_pos.mpr after) (neg_pos.mpr negative)]
    exact proper i vanishes_open
  let Active := {i : ι // (rim i).Nonempty}
  have segments (i : Active) : ∃ a ∈ rim i.val, ∃ b ∈ rim i.val,
      rim i.val = segment ℝ a b := by
    have compact_rim : IsCompact (rim i.val) := compact.inter_right
      (isClosed_eq (equation i.val).continuous_of_finiteDimensional continuous_const)
    have convex := (convex_nonpositiveRegion equation).inter
      ((convex_singleton (0 : ℝ)).affine_preimage (equation i.val))
    exact exists_segment_of_compact_convex_collinear compact_rim convex i.property
      (collinear_of_affine_zero (equation i.val) (proper i.val) (fun _ h => h.2))
  choose first first_mem last last_mem equal using segments
  let edges := Set.range (fun i : Active => (first i, last i))
  refine ⟨edges, Set.finite_range _, ?_⟩
  ext x
  constructor
  · intro boundary
    obtain ⟨i, zero⟩ := nonpositiveRegion_frontier_support equation boundary
    have member : x ∈ rim i :=
      ⟨(isClosed_nonpositiveRegion equation).frontier_subset boundary, zero⟩
    let active : Active := ⟨i, ⟨x, member⟩⟩
    exact Set.mem_iUnion₂.mpr ⟨(first active, last active), ⟨active, rfl⟩,
      (Set.ext_iff.mp (equal active) x).mp member⟩
  · intro inside
    obtain ⟨edge, ⟨i, rfl⟩, in_segment⟩ := Set.mem_iUnion₂.mp inside
    exact rim_boundary i.val ((Set.ext_iff.mp (equal i) x).mpr in_segment)

end Unfoldings
