module

public import Unfoldings.Topology.BoundaryAtlas
public import Unfoldings.Topology.PlanarHalfPlane

/-!
# Boundary atlases identify the frontier of every planar embedding

An injective open planar patch cannot hit a half-plane chart's boundary
center. For compact spaces this separates the marked boundary image from the
interior of the embedded image. An open planar model of the boundary complement
supplies the reverse inclusion, identifying its exact frontier.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

open PlanarTopology

variable {X : Type*} [TopologicalSpace X] {B : Set X} {x : X}

theorem HalfPlaneBoundaryChart.not_mem_range_of_planar_injection
    (N : HalfPlaneBoundaryChart B x) {A : Type*} [TopologicalSpace A]
    (i : A → Plane) (embedding : Topology.IsOpenEmbedding i) (f : C(A, X))
    (injective : Function.Injective f) : x ∉ Set.range f := by
  rintro ⟨a, equal⟩
  let D : Set A := f ⁻¹' N.source
  have open_D : IsOpen D := N.open_source.preimage f.continuous
  let into : C(D, N.source) := ⟨fun z => ⟨f z.val, z.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let g : C(D, closedHalfPlane) := ⟨fun z => (N.chart (into z)).val,
    continuous_subtype_val.comp (N.chart.continuous.comp into.continuous)⟩
  have inj : Function.Injective g := by
    intro p q same
    have points := N.chart.injective (Subtype.ext same)
    exact Subtype.ext (injective (congrArg (fun p : N.source => p.val) points))
  have source_embedding : Topology.IsOpenEmbedding (fun z : D => i z.val) :=
    embedding.comp open_D.isOpenEmbedding_subtypeVal
  let z : D := ⟨a, by change f a ∈ N.source; rw [equal]; exact N.mem_source⟩
  have center : into z = ⟨x, N.mem_source⟩ := Subtype.ext equal
  have positive := positive_snd_of_planar_injection _ source_embedding g inj z
  change 0 < (N.chart (into z)).val.val.2 at positive
  rw [center, N.center] at positive
  exact lt_irrefl 0 positive

theorem halfPlane_neighborhood_has_interior {U : Set closedHalfPlane} (open_U : IsOpen U)
    (center : halfPlaneOrigin ∈ U) : ∃ p ∈ U, 0 < p.val.2 := by
  obtain ⟨r, positive, ball⟩ := Metric.isOpen_iff.mp open_U halfPlaneOrigin center
  let p : closedHalfPlane := ⟨(0, r / 2), by change (0 : ℝ) ≤ r / 2; positivity⟩
  refine ⟨p, ball ?_, half_pos positive⟩
  change dist (0, r / 2) (0 : ℝ × ℝ) < r
  rw [Prod.dist_eq]
  change max (dist (0 : ℝ) 0) (dist (r / 2) 0) < r
  rw [dist_self, Real.dist_eq, sub_zero, abs_of_pos (half_pos positive),
    max_eq_right (half_pos positive).le]
  linarith

theorem boundary_compl_nonempty_of_halfPlaneCharts (nonempty : B.Nonempty)
    (charts : ∀ x ∈ B, Nonempty (HalfPlaneBoundaryChart B x)) : Bᶜ.Nonempty := by
  obtain ⟨x, hx⟩ := nonempty
  obtain ⟨N⟩ := charts x hx
  have center : halfPlaneOrigin ∈ N.target := by
    rw [← N.center]
    exact (N.chart ⟨x, N.mem_source⟩).property
  obtain ⟨p, hp, positive⟩ := halfPlane_neighborhood_has_interior N.open_target center
  let y := N.chart.symm ⟨p, hp⟩
  refine ⟨y.val, ?_⟩
  intro boundary
  have on_line := (N.boundary y).mp boundary
  rw [N.chart.apply_symm_apply] at on_line
  exact positive.ne' on_line

theorem interior_range_nonempty_of_open_compl (i : ↥(Bᶜ) → Plane)
    (embedding : Topology.IsOpenEmbedding i) (f : C(X, Plane)) (injective : Function.Injective f)
    (outside : Bᶜ.Nonempty) : (interior (Set.range f)).Nonempty := by
  let g : C(↥(Bᶜ), Plane) := ⟨fun z => f z.val, f.continuous.comp continuous_subtype_val⟩
  have inj : Function.Injective g := fun _ _ equal => Subtype.ext (injective equal)
  have open_range := isOpen_range_of_openEmbedding i embedding g inj
  have included : Set.range g ⊆ Set.range f := by rintro _ ⟨z, rfl⟩; exact ⟨z.val, rfl⟩
  obtain ⟨x, hx⟩ := outside
  exact ⟨f x, interior_mono included (open_range.interior_eq.symm ▸
    (show f x ∈ Set.range g from ⟨⟨x, hx⟩, rfl⟩))⟩

theorem frontier_range_eq_boundaryImage [CompactSpace X] [T2Space X]
    (charts : ∀ x ∈ B, Nonempty (HalfPlaneBoundaryChart B x))
    (i : ↥(Bᶜ) → Plane) (embedding : Topology.IsOpenEmbedding i)
    (f : C(X, Plane)) (injective : Function.Injective f) :
    frontier (Set.range f) = f '' B := by
  let embedded := f.continuous.isClosedEmbedding injective
  let e : X ≃ₜ Set.range f := embedded.isEmbedding.toHomeomorph
  let g : C(↥(Bᶜ), Plane) := ⟨fun z => f z.val, f.continuous.comp continuous_subtype_val⟩
  have inj : Function.Injective g := fun _ _ equal => Subtype.ext (injective equal)
  have open_range := isOpen_range_of_openEmbedding i embedding g inj
  have included : Set.range g ⊆ Set.range f := by rintro _ ⟨z, rfl⟩; exact ⟨z.val, rfl⟩
  ext y
  constructor
  · intro boundary
    have member : y ∈ Set.range f := by
      rw [← embedded.isClosed_range.closure_eq]
      exact frontier_subset_closure boundary
    obtain ⟨x, rfl⟩ := member
    by_cases marked : x ∈ B
    · exact ⟨x, marked, rfl⟩
    · exfalso
      have inside : f x ∈ interior (Set.range f) :=
        interior_mono included (open_range.interior_eq.symm ▸
          (show f x ∈ Set.range g from ⟨⟨x, marked⟩, rfl⟩))
      exact ((mem_frontier_iff_notMem_interior (Set.mem_range_self x)).mp boundary) inside
  · rintro ⟨x, marked, rfl⟩
    apply (mem_frontier_iff_notMem_interior (Set.mem_range_self x)).mpr
    intro inside
    obtain ⟨N⟩ := charts x marked
    let U := interior (Set.range f)
    let fromPlane : C(U, X) := ⟨fun z => e.symm ⟨z.val, interior_subset z.property⟩, by fun_prop⟩
    have inj_fromPlane : Function.Injective fromPlane := by
      intro p q equal
      have points := e.symm.injective equal
      exact Subtype.ext (congrArg (fun z : Set.range f => z.val) points)
    apply N.not_mem_range_of_planar_injection Subtype.val
      isOpen_interior.isOpenEmbedding_subtypeVal fromPlane inj_fromPlane
    refine ⟨⟨f x, inside⟩, ?_⟩
    change e.symm (e x) = x
    exact e.symm_apply_apply x

end Unfoldings
