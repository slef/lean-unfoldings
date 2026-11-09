module

public import Unfoldings.Geometry.SegmentVertices
public import Unfoldings.Topology.FiniteSubdivision

/-! Subdivide a segment at a finite set of marked points, retaining exact coverage. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_unmarked_subsegment {V : Set E} (finite : V.Finite) {a b x : E}
    (ha : a ∈ V) (hb : b ∈ V) (hx : x ∈ segment ℝ a b) (unmarked : x ∉ V) :
    ∃ c ∈ V, ∃ d ∈ V, c ≠ d ∧ x ∈ openSegment ℝ c d ∧
      segment ℝ c d ⊆ segment ℝ a b ∧ Disjoint V (openSegment ℝ c d) := by
  have different : a ≠ b := by
    intro equal
    have same : x = a := by simpa only [equal, segment_same, Set.mem_singleton_iff] using hx
    exact unmarked (same ▸ ha)
  let coordinate := lineCoordinate a b
  let T := coordinate '' (V ∩ segment ℝ a b)
  have finite_T : T.Finite := (finite.inter_of_left _).image _
  have left : coordinate a = 0 := by simpa using lineCoordinate_lineMap different 0
  have right : coordinate b = 1 := by simpa using lineCoordinate_lineMap different 1
  have zero : (0 : ℝ) ∈ T := ⟨a, ⟨ha, left_mem_segment ℝ a b⟩, left⟩
  have one : (1 : ℝ) ∈ T := ⟨b, ⟨hb, right_mem_segment ℝ a b⟩, right⟩
  have inside : coordinate x ∈ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨t, ht, equal⟩ := (segment_eq_image_lineMap ℝ a b).le hx
    change lineCoordinate a b x ∈ Set.Icc (0 : ℝ) 1
    rw [← equal, lineCoordinate_lineMap different]
    exact ht
  have outside : coordinate x ∉ T := by
    rintro ⟨y, ⟨hy, member⟩, equal⟩
    have same := lineCoordinate_injective different (segment_subset_line a b member)
      (segment_subset_line a b hx) equal
    exact unmarked (same ▸ hy)
  obtain ⟨u, hu, v, hv, _, before, after, _, gap⟩ :=
    exists_marked_gap finite_T zero one inside outside
  obtain ⟨c, ⟨hc, c_on⟩, at_c⟩ := hu
  obtain ⟨d, ⟨hd, d_on⟩, at_d⟩ := hv
  have ordered : u < v := before.trans after
  have ends_different : c ≠ d := by
    intro equal
    have same : u = v := at_c.symm.trans ((congrArg coordinate equal).trans at_d)
    exact ordered.ne same
  have c_line := segment_subset_line a b c_on
  have d_line := segment_subset_line a b d_on
  have covers : x ∈ openSegment ℝ c d := by
    apply (lineCoordinate_mem_openSegment_iff different ends_different c_line d_line
      (segment_subset_line a b hx)).mpr
    change coordinate x ∈ Set.Ioo (min (coordinate c) (coordinate d))
      (max (coordinate c) (coordinate d))
    rw [at_c, at_d, min_eq_left ordered.le, max_eq_right ordered.le]
    exact ⟨before, after⟩
  have included := (convex_segment (𝕜 := ℝ) a b).segment_subset c_on d_on
  refine ⟨c, hc, d, hd, ends_different, covers, included, Set.disjoint_left.mpr ?_⟩
  intro y hy member
  have in_parent := included (openSegment_subset_segment ℝ c d member)
  have marked : coordinate y ∈ T := ⟨y, ⟨hy, in_parent⟩, rfl⟩
  have between := (lineCoordinate_mem_openSegment_iff different ends_different c_line d_line
    (segment_subset_line a b in_parent)).mp member
  change coordinate y ∈ Set.Ioo (min (coordinate c) (coordinate d))
    (max (coordinate c) (coordinate d)) at between
  rw [at_c, at_d, min_eq_left ordered.le, max_eq_right ordered.le] at between
  exact Set.disjoint_left.mp gap marked between

end Unfoldings
