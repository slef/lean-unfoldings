module

public import Unfoldings.Geometry.RadialTriangleEdges
public import Unfoldings.Topology.SphereFiniteCoverage

/-! A finite radial triangle family covers the sphere once its open edges are paired. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Module

local notation "Sphere" => Subtype (fun p : Space => p ∈ Metric.sphere (0 : Space) 1)

/-- A section of the cone over a chord triangle is closed in the unit sphere. -/
theorem isClosed_radialTriangle_on_sphere (b : Basis (Fin 3) ℝ Space) :
    IsClosed {x : Sphere | x.val ∈ positiveRadialHull (convexHull ℝ (Set.range b))} := by
  have same : {x : Sphere | x.val ∈ positiveRadialHull (convexHull ℝ (Set.range b))} =
      ⋂ i : Fin 3, {x : Sphere | 0 ≤ b.coord i x.val} := by
    ext x
    rw [Set.mem_iInter]
    have n : ‖x.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    have nz : x.val ≠ 0 := by intro zero; rw [zero, norm_zero] at n; norm_num at n
    exact mem_positiveRadialHull_triangle_iff b nz
  rw [same]
  exact isClosed_iInter (fun i => isClosed_le continuous_const
    ((b.coord i).continuous_of_finiteDimensional.comp continuous_subtype_val))

/-- A unit point supported on one vertex, with nonnegative coordinates, is that vertex. -/
theorem eq_triangle_vertex_of_single_coord (b : Basis (Fin 3) ℝ Space)
    (unit : ∀ i, ‖b i‖ = 1) {x : Space} (x_unit : ‖x‖ = 1) {j : Fin 3}
    (nonnegative : 0 ≤ b.coord j x) (zero : ∀ i ≠ j, b.coord i x = 0) :
    x = b j := by
  have expanded : (∑ i, b.coord i x • b i) = x := b.sum_repr x
  rw [Finset.sum_eq_single j (fun i _ hi => by rw [zero i hi, zero_smul])
    (fun absent => (absent (Finset.mem_univ _)).elim)] at expanded
  have scale := congrArg norm expanded
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg nonnegative, unit, mul_one, x_unit] at scale
  rw [scale, one_smul] at expanded
  exact expanded.symm

/-- At a strict shared-edge point, the two tangential coordinates are
identical in the two named frames. -/
theorem triangle_tangent_coords_eq (b c : Basis (Fin 3) ℝ Space)
    (first : b 0 = c 0) (last : b 1 = c 1) {x : Space} (edge : b.coord 2 x = 0) :
    c.coord 0 x = b.coord 0 x ∧ c.coord 1 x = b.coord 1 x := by
  have expand : (∑ i, b.coord i x • b i) = x := b.sum_repr x
  rw [Fin.sum_univ_three, edge, zero_smul, add_zero, first, last] at expand
  constructor
  · conv_lhs => rw [← expand]
    simp [Basis.coord_apply, c.repr_self, Finsupp.single_apply]
  · conv_lhs => rw [← expand]
    simp [Basis.coord_apply, c.repr_self, Finsupp.single_apply]

set_option maxHeartbeats 1000000 in
-- The cover is assembled by pulling local cone neighborhoods to the sphere.
/-- Every nonvertex point becomes interior as soon as each triangle edge
has an opposing triangle with the same two endpoint sites. -/
theorem iUnion_radialTriangles_eq_unitSphere {I : Type*} [Fintype I] [Nonempty I]
    (b : I → Basis (Fin 3) ℝ Space) (unit : ∀ i j, ‖b i j‖ = 1)
    (paired : ∀ (i : I) (σ : Equiv.Perm (Fin 3)), ∃ (j : I) (τ : Equiv.Perm (Fin 3)),
      let B := (b i).reindex σ
      let C := (b j).reindex τ
      B 0 = C 0 ∧ B 1 = C 1 ∧ B.coord 2 (C 2) < 0)
    (has_face : ∃ (x : Sphere) (i : I),
      x.val ∈ positiveRadialHull (convexHull ℝ (Set.range (b i))) ∧
        ∀ j k, x.val ≠ b j k) :
    (⋃ i, {x : Sphere | x.val ∈ positiveRadialHull (convexHull ℝ (Set.range (b i)))}) = Set.univ := by
  let patch := ⋃ i, {x : Sphere | x.val ∈ positiveRadialHull (convexHull ℝ (Set.range (b i)))}
  let vertex (ij : I × Fin 3) : Sphere :=
    ⟨b ij.1 ij.2, Metric.mem_sphere.mpr ((dist_zero_right _).trans (unit ij.1 ij.2))⟩
  let vertices := Set.range vertex
  apply unitSphere_eq_univ_of_finite_boundary (vertices := vertices)
  · exact isClosed_iUnion_of_finite (fun i => isClosed_radialTriangle_on_sphere (b i))
  · exact Set.finite_range vertex
  · exact Set.range_nonempty _
  · rintro x ⟨⟨i,j⟩, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, 1, one_pos, b i j, subset_convexHull ℝ _ (Set.mem_range_self j),
      (one_smul ℝ (b i j)).symm⟩
  · rintro x ⟨member, nonvertex⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
    have x_unit : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    have nz : x.val ≠ 0 := by intro zero; rw [zero, norm_zero] at x_unit; norm_num at x_unit
    have some_vertex (j : Fin 3) : x.val ≠ b i j :=
      fun equal => nonvertex ⟨(i,j), Subtype.ext equal.symm⟩
    have local_to_sphere {U : Set Space} (cover : ∀ z : Sphere, z.val ∈ U → z ∈ patch)
        (inside : x.val ∈ interior U) : x ∈ interior patch := by
      apply mem_interior_iff_mem_nhds.mpr
      apply Filter.mem_of_superset ((isOpen_interior.preimage continuous_subtype_val).mem_nhds inside)
      exact fun z hz => cover z (interior_subset hz)
    by_cases inside : ∀ j, 0 < (b i).coord j x.val
    · exact local_to_sphere (fun z hz => Set.mem_iUnion.mpr ⟨i,hz⟩)
        (mem_interior_positiveRadialHull_triangle (b i) inside)
    push Not at inside
    obtain ⟨e, no_pos⟩ := inside
    let σ := Equiv.swap e (2 : Fin 3)
    obtain ⟨j, τ, first, last, opposite⟩ := paired i σ
    let B := (b i).reindex σ
    let C := (b j).reindex τ
    have range_B : Set.range B = Set.range (b i) := by
      rw [Basis.coe_reindex, (Equiv.surjective _).range_comp]
    have range_C : Set.range C = Set.range (b j) := by
      rw [Basis.coe_reindex, (Equiv.surjective _).range_comp]
    have lower : ∀ k, 0 ≤ B.coord k x.val := (mem_positiveRadialHull_triangle_iff B nz).mp
      (range_B.symm ▸ hi)
    have at_edge : B.coord 2 x.val = 0 := by
      apply le_antisymm _ (lower 2)
      change B.repr x.val 2 ≤ 0
      rw [Basis.repr_reindex_apply, Equiv.symm_swap, Equiv.swap_apply_right]
      exact no_pos
    have B_unit (k : Fin 3) : ‖B k‖ = 1 := by rw [Basis.reindex_apply]; exact unit _ _
    have not_B_vertex (k : Fin 3) : x.val ≠ B k := by
      rw [Basis.reindex_apply]
      exact some_vertex _
    have left : 0 < B.coord 0 x.val := by
      by_contra! failure
      apply not_B_vertex 1
      refine eq_triangle_vertex_of_single_coord B B_unit x_unit (lower 1) ?_
      intro k different
      fin_cases k
      · exact le_antisymm failure (lower 0)
      · exact (different rfl).elim
      · exact at_edge
    have right : 0 < B.coord 1 x.val := by
      by_contra! failure
      apply not_B_vertex 0
      refine eq_triangle_vertex_of_single_coord B B_unit x_unit (lower 0) ?_
      intro k different
      fin_cases k
      · exact (different rfl).elim
      · exact le_antisymm failure (lower 1)
      · exact at_edge
    obtain ⟨left_eq, right_eq⟩ := triangle_tangent_coords_eq B C first last at_edge
    apply local_to_sphere (U := positiveRadialHull (convexHull ℝ (Set.range B)) ∪
      positiveRadialHull (convexHull ℝ (Set.range C)))
    · intro z hz
      rcases hz with in_B | in_C
      · exact Set.mem_iUnion.mpr ⟨i, range_B ▸ in_B⟩
      · exact Set.mem_iUnion.mpr ⟨j, range_C ▸ in_C⟩
    · exact mem_interior_radialTriangle_union_of_opposite first last opposite left right
        (left_eq.symm ▸ left) (right_eq.symm ▸ right)
  · obtain ⟨x, i, hx, excluded⟩ := has_face
    exact ⟨x, Set.mem_iUnion.mpr ⟨i, hx⟩, fun ⟨⟨j,k⟩, equal⟩ =>
      excluded j k (congrArg Subtype.val equal).symm⟩

end Unfoldings
