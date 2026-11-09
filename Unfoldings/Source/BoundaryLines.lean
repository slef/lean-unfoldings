module

public import Unfoldings.Source.CutSupport
public import Unfoldings.Source.CutConnected
public import Unfoldings.Source.CompletedPieces
public import Unfoldings.Geometry.AffineSupport

/-!
# A finite affine-line support for the developed source boundary

The support equations are nonzero affine functions, so none represents the
whole plane. Transporting the finite original-face support by the proved finite
actual motions gives finitely many lines containing the entire net boundary.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem exists_finite_source_cut_equations :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (base : C.PointFiber Set.univ source),
      ∃ L : Set (Plane →ᵃ[ℝ] ℝ), L.Finite ∧ (∀ l ∈ L, l ≠ 0) ∧
        ∀ f : Face, ∀ x ∈ P.sourceFaceCutSupport R base f, ∃ l ∈ L, l x = 0 := by
  let := P.metricSpace
  intro source R base
  let pairs := {a ∈ P.sourceImages R base ×ˢ P.sourceImages R base | a.1 ≠ a.2}
  let bisectors := (fun a : Plane × Plane => bisectorFunction a.1 a.2) '' pairs
  let edges := Set.range (fun i : Face × Fin 3 => (C.triangle i.1).coord i.2)
  have finite_pairs : pairs.Finite :=
    ((P.finite_sourceImages R base).prod (P.finite_sourceImages R base)).subset
      (fun _ member => member.1)
  refine ⟨bisectors ∪ edges, (finite_pairs.image _).union (Set.finite_range _), ?_, ?_⟩
  · intro l member
    rcases member with ⟨a, ha, rfl⟩ | ⟨⟨f, i⟩, rfl⟩
    · exact bisectorFunction_ne_zero ha.2
    · exact (C.triangle f).coord_ne_zero i
  · intro f x member
    rcases member with bisector | edge
    · obtain ⟨v, hv, w, hw, different, lengths⟩ := by
        simpa only [sourceBisectors, Set.mem_iUnion, Set.mem_ofPred_eq] using bisector
      exact ⟨bisectorFunction v w, Or.inl ⟨(v, w), ⟨⟨hv, hw⟩, different⟩, rfl⟩,
        (bisectorFunction_eq_zero_iff v w x).mpr lengths⟩
    · obtain ⟨i, zero⟩ := Set.mem_iUnion.mp edge
      exact ⟨(C.triangle f).coord i, Or.inr ⟨(f, i), rfl⟩, zero⟩

theorem exists_finite_source_boundary_equations :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      ∃ L : Set (Plane →ᵃ[ℝ] ℝ), L.Finite ∧ (∀ l ∈ L, l ≠ 0) ∧
        ∀ z ∈ frontier R.domain, ∃ l ∈ L, l z = 0 := by
  let := P.metricSpace
  intro source R
  obtain ⟨base, base_point⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) source
  let b : C.PointFiber Set.univ source := ⟨base, base_point⟩
  obtain ⟨L, finite_L, nonzero, supports⟩ := P.exists_finite_source_cut_equations R b
  obtain ⟨M, finite_M, pieces⟩ := P.exists_finite_completed_face_pieces R
  let equations := (fun p : (Plane →ᵃ[ℝ] ℝ) × (Plane ≃ᵃⁱ[ℝ] Plane) =>
    p.1.comp p.2.symm.toAffineMap) '' (L ×ˢ M)
  refine ⟨equations, (finite_L.prod finite_M).image _, ?_, ?_⟩
  · rintro l ⟨⟨k, A⟩, ⟨hk, hA⟩, rfl⟩
    exact affine_comp_equiv_ne_zero k (nonzero k hk) A.symm
  · intro z boundary
    let point : R.domain := ⟨z, R.closed_domain.frontier_subset boundary⟩
    obtain ⟨A, hA, f, y, developed, image⟩ := pieces point
    have cut : C.faceMap Set.univ f y ∈ sourceCutLocus source := by
      rw [← image, ← P.sourceDomain_boundary_projection_cutLocus R]
      exact ⟨point, boundary, rfl⟩
    have support : y.val ∈ P.sourceFaceCutSupport R b f := by
      by_cases inside : y.val ∈ interior (C.triangle f).carrier
      · exact Or.inl (P.cut_face_interior_mem_sourceBisectors R b f y inside cut)
      · obtain ⟨i, zero⟩ := (C.triangle f).exists_coord_eq_zero_of_not_interior y.property inside
        exact Or.inr (Set.mem_iUnion.mpr ⟨i, zero⟩)
    obtain ⟨l, hl, zero⟩ := supports f y.val support
    refine ⟨l.comp A.symm.toAffineMap, ⟨(l, A), ⟨hl, hA⟩, rfl⟩, ?_⟩
    change l (A.symm z) = 0
    change z = A y.val at developed
    rw [developed, A.symm_apply_apply]
    exact zero

end Unfoldings.SpatialFolding.ConvexBoundary
