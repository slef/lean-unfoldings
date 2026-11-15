module

public import Unfoldings.Cone.ReentrantSectorTopology
public import Unfoldings.Geometry.ComplexLineEquation
public import Unfoldings.Geometry.AffineArrangement
public import Unfoldings.Geometry.SegmentEndpointGerm

/-! The two exact bank rays are precisely the frontier of a geometric reentrant sector. -/

@[expose] public section

noncomputable section

open Topology
open scoped NNReal

namespace Unfoldings

/-- Two genuine closed pieces with a thin common bank have complementary open interiors. -/
theorem interior_eq_compl_of_regular_closed_cover {E : Type*} [TopologicalSpace E]
    {s t : Set E} (closed_t : IsClosed t) (regular_t : closure (interior t) = t)
    (cover : s ∪ t = Set.univ) (thin : interior (s ∩ t) = ∅) : interior s = tᶜ := by
  have disjoint : Disjoint (interior s) (interior t) := by
    apply Set.disjoint_left.mpr
    intro x first last
    have member : x ∈ interior (s ∩ t) := by
      rw [interior_inter]
      exact ⟨first, last⟩
    simp only [thin, Set.mem_empty_iff_false] at member
  have against_closed : Disjoint (interior s) t := by
    rw [← regular_t]
    exact disjoint.closure_right isOpen_interior
  apply Set.Subset.antisymm
  · exact Set.disjoint_left.mp against_closed
  · apply interior_maximal _ closed_t.isOpen_compl
    intro x outside
    have member : x ∈ s ∪ t := by rw [cover]; trivial
    exact member.resolve_right outside

/-- Any two original geometric rays have empty planar interior, including coincident rays. -/
theorem interior_two_rays_eq_empty (d e : ℂ) :
    interior (nonnegativeRay d ∪ nonnegativeRay e) = ∅ := by
  let f : Bool → ℂ →ᵃ[ℝ] ℝ :=
    fun b => if b then complexLineEquation 0 d else complexLineEquation 0 e
  have nonzero (b : Bool) : f b ≠ 0 := by
    cases b <;> exact complexLineEquation_ne_zero _ _
  have included : nonnegativeRay d ∪ nonnegativeRay e ⊆ {z | ∀ b, f b z ≠ 0}ᶜ := by
    intro z member regular
    rcases member with ⟨t, _nonnegative, rfl⟩ | ⟨t, _nonnegative, rfl⟩
    · apply regular true
      have on_line := complexLineEquation_lineMap (0 : ℂ) d t
      simpa [f, AffineMap.lineMap_apply_module'] using on_line
    · apply regular false
      have on_line := complexLineEquation_lineMap (0 : ℂ) e t
      simpa [f, AffineMap.lineMap_apply_module'] using on_line
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have member := interior_mono included hz
  rw [(AffineArrangement.dense_regular f nonzero).interior_compl] at member
  exact member

/-- Reentrant sectors and their complement have no common open region. -/
theorem interior_closedAngularSector_inter_complementary (width : ℝ) (positive : 0 < width)
    (small : width < 2 * Real.pi) :
    interior (closedAngularSector width ∩ complementarySector width) = ∅ := by
  rw [closedAngularSector_inter_complementary width positive small]
  have included : Set.range (fun r : ℝ≥0 => (r : ℂ)) ∪
      Set.range (fun r : ℝ≥0 => (r : ℂ) * polarRay width) ⊆
        nonnegativeRay (1 : ℂ) ∪ nonnegativeRay (polarRay width) := by
    rintro z (⟨r, rfl⟩ | ⟨r, rfl⟩)
    · exact Or.inl ⟨r, r.coe_nonneg, by simp [Complex.real_smul]⟩
    · exact Or.inr ⟨r, r.coe_nonneg, by rw [Complex.real_smul]⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have member := interior_mono included hz
  rw [interior_two_rays_eq_empty] at member
  exact member

theorem isClosed_complementarySector (width : ℝ) (positive : 0 < width)
    (small : width < 2 * Real.pi) : IsClosed (complementarySector width) :=
  (rotation (Circle.exp width)).toHomeomorph.isClosedMap _
    (isClosed_closedAngularSector (2 * Real.pi - width) (sub_pos.mpr small) (by linarith))

theorem closure_interior_complementarySector (width : ℝ) (positive : 0 < width)
    (small : width < 2 * Real.pi) : closure (interior (complementarySector width)) =
      complementarySector width := by
  let H := (rotation (Circle.exp width)).toHomeomorph
  change closure (interior (H '' closedAngularSector (2 * Real.pi - width))) =
    H '' closedAngularSector (2 * Real.pi - width)
  rw [← H.image_interior, ← H.image_closure,
    closure_interior_closedAngularSector (2 * Real.pi - width) (sub_pos.mpr small) (by linarith)]

/-- The complementary region is exactly the complement of the sector's geometric interior. -/
theorem interior_closedAngularSector_eq_compl (width : ℝ) (positive : 0 < width)
    (small : width < 2 * Real.pi) : interior (closedAngularSector width) =
      (complementarySector width)ᶜ :=
  interior_eq_compl_of_regular_closed_cover (isClosed_complementarySector width positive small)
    (closure_interior_complementarySector width positive small)
    (closedAngularSector_union_complementary width)
    (interior_closedAngularSector_inter_complementary width positive small)

/-- The actual physical frontier consists precisely of the initial and terminal banks. -/
theorem frontier_closedAngularSector (width : ℝ) (positive : 0 < width)
    (small : width < 2 * Real.pi) : frontier (closedAngularSector width) =
      Set.range (fun r : ℝ≥0 => (r : ℂ)) ∪
        Set.range (fun r : ℝ≥0 => (r : ℂ) * polarRay width) := by
  rw [frontier, (isClosed_closedAngularSector width positive small).closure_eq,
    interior_closedAngularSector_eq_compl width positive small, Set.sdiff_compl,
    closedAngularSector_inter_complementary width positive small]

/-- The open geometric sector retains precisely the strict real headings and positive radii. -/
theorem mem_interior_closedAngularSector_iff_polar (width : ℝ) (positive : 0 < width)
    (small : width < 2 * Real.pi) (z : ℂ) : z ∈ interior (closedAngularSector width) ↔
      ∃ r : ℝ, 0 < r ∧ ∃ θ ∈ Set.Ioo 0 width, z = (r : ℂ) * polarRay θ := by
  constructor
  · intro inside
    obtain ⟨r, θ, bounds, equal⟩ := interior_subset inside
    have not_bank : z ∉ Set.range (fun r : ℝ≥0 => (r : ℂ)) ∪
        Set.range (fun r : ℝ≥0 => (r : ℂ) * polarRay width) := by
      rw [← frontier_closedAngularSector width positive small]
      exact fun boundary => boundary.2 inside
    have nonzero : r ≠ 0 := by
      intro zero
      apply not_bank
      apply Or.inl
      refine ⟨0, ?_⟩
      simpa only [zero, NNReal.coe_zero, Complex.ofReal_zero, zero_mul] using equal.symm
    have first : θ ≠ 0 := by
      intro at_start
      exact not_bank (Or.inl ⟨r, by simpa only [at_start, polarRay_zero, mul_one] using equal.symm⟩)
    have last : θ ≠ width := by
      intro at_finish
      exact not_bank (Or.inr ⟨r, by simpa only [at_finish] using equal.symm⟩)
    exact ⟨r, NNReal.coe_pos.mpr (lt_of_le_of_ne zero_le (Ne.symm nonzero)), θ,
      ⟨lt_of_le_of_ne bounds.1 first.symm, lt_of_le_of_ne bounds.2 last⟩, equal⟩
  · rintro ⟨r, radius, θ, heading, rfl⟩
    exact polar_mem_interior_closedAngularSector width r θ radius heading

/-- The whole interior of either convex or reentrant sectors is connected. -/
theorem isPreconnected_interior_closedAngularSector (width : ℝ) (positive : 0 < width)
    (small : width < 2 * Real.pi) : IsPreconnected (interior (closedAngularSector width)) := by
  let f : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * polarRay p.2
  have continuous_f : Continuous f := by unfold f polarRay; fun_prop
  have same : interior (closedAngularSector width) =
      f '' (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 width) := by
    ext z
    rw [mem_interior_closedAngularSector_iff_polar width positive small]
    constructor
    · rintro ⟨r, radius, θ, heading, equal⟩
      exact ⟨(r, θ), ⟨radius, heading⟩, equal.symm⟩
    · rintro ⟨⟨r, θ⟩, ⟨radius, heading⟩, equal⟩
      exact ⟨r, radius, θ, heading, equal.symm⟩
  rw [same]
  exact ((convex_Ioi (0 : ℝ)).prod (convex_Ioo (0 : ℝ) width)).isPreconnected.image
    f continuous_f.continuousOn

end Unfoldings
