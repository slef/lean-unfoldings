module

public import Mathlib.Geometry.Euclidean.Sphere.SecondInter
public import Mathlib.Topology.Algebra.Module.Cardinality

/-! Finite exceptional radii cannot hide disagreement along a nontrivial convex contact set. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A nonconstant affine line meets finitely many concentric spheres at finitely many parameters. -/
theorem finite_lineMap_radius_parameters {p q : V} (different : p ≠ q)
    (center : V) {exception : Set ℝ} (finite : exception.Finite) :
    {s : ℝ | ‖AffineMap.lineMap (k := ℝ) p q s - center‖ ∈ exception}.Finite := by
  have fiber (radius : ℝ) :
      {s : ℝ | ‖AffineMap.lineMap (k := ℝ) p q s - center‖ = radius}.Finite := by
    let sphere : EuclideanGeometry.Sphere V := ⟨center, radius⟩
    let points := Set.range (AffineMap.lineMap (k := ℝ) p q) ∩ (sphere : Set V)
    have points_finite : points.Finite := by
      by_cases nonempty : points.Nonempty
      · obtain ⟨_, ⟨a, rfl⟩, on_sphere⟩ := nonempty
        apply ((Set.finite_singleton (sphere.secondInter
          (AffineMap.lineMap (k := ℝ) p q a) (q - p))).insert
            (AffineMap.lineMap (k := ℝ) p q a)).subset
        rintro _ ⟨⟨b, rfl⟩, member⟩
        have on_line : AffineMap.lineMap (k := ℝ) p q b ∈
            AffineSubspace.mk' (AffineMap.lineMap (k := ℝ) p q a) (ℝ ∙ (q - p)) := by
          rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton]
          refine ⟨b - a, ?_⟩
          simp only [AffineMap.lineMap_apply_module', vsub_eq_sub]
          module
        exact (sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem
          on_sphere on_line).mpr member
      · exact Set.finite_empty.subset (Set.not_nonempty_iff_eq_empty.mp nonempty).subset
    have preimage := points_finite.preimage (AffineMap.lineMap_injective ℝ different).injOn
    apply preimage.subset
    intro s member
    refine ⟨⟨s, rfl⟩, ?_⟩
    change ‖AffineMap.lineMap (k := ℝ) p q s - center‖ = radius at member
    change dist (AffineMap.lineMap (k := ℝ) p q s) center = radius
    simpa only [dist_eq_norm] using member
  have union_finite := finite.biUnion (fun radius _ => fiber radius)
  apply union_finite.subset
  intro s member
  exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨member, rfl⟩⟩

/-- Continuous functions agreeing off finitely many spheres agree on every nontrivial convex set.
This also applies to a segment of closed boundary contact, whose ambient interior is empty. -/
theorem eqOn_convex_of_finite_radius_exceptions
    {W : Type*} [TopologicalSpace W] [T2Space W]
    {A : Set V} (convex : Convex ℝ A) (nontrivial : A.Nontrivial)
    {f g : V → W} (first : Continuous f) (last : Continuous g)
    (center : V) {exception : Set ℝ} (finite : exception.Finite)
    (agree : ∀ z ∈ A, ‖z - center‖ ∉ exception → f z = g z) : Set.EqOn f g A := by
  intro p member
  obtain ⟨q, other, different⟩ := nontrivial.exists_ne p
  let line := AffineMap.lineMap (k := ℝ) p q
  let bad := {s : ℝ | ‖line s - center‖ ∈ exception}
  have bad_finite : bad.Finite := finite_lineMap_radius_parameters different.symm center finite
  have dense_good := bad_finite.countable.dense_compl ℝ
  let good := badᶜ ∩ Set.Ioo (0 : ℝ) 1
  have approached : (0 : ℝ) ∈ closure good := by
    have dense_interval : Set.Ioo (0 : ℝ) 1 ⊆ closure good :=
      fun s inside => isOpen_Ioo.closure_inter ⟨dense_good s, inside⟩
    apply closure_minimal dense_interval isClosed_closure
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, zero_le_one⟩
  have closed : IsClosed {s : ℝ | f (line s) = g (line s)} :=
    isClosed_eq (first.comp AffineMap.lineMap_continuous)
      (last.comp AffineMap.lineMap_continuous)
  have good_agrees : good ⊆ {s : ℝ | f (line s) = g (line s)} := by
    rintro s ⟨outside, bounds⟩
    apply agree (line s)
    · exact convex.segment_subset member other
        (lineMap_mem_segment ℝ p q ⟨bounds.1.le, bounds.2.le⟩)
    · exact outside
  have equal := closure_minimal good_agrees closed approached
  change f (line 0) = g (line 0) at equal
  simpa only [line, AffineMap.lineMap_apply_zero] using equal

end Unfoldings
