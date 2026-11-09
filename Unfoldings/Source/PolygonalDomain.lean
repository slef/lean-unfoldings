module

public import Unfoldings.Source.BoundaryLines
public import Unfoldings.Geometry.AffineArrangement

/-!
# The completed source domain is a finite polygonal region

The polygons are compact intersections of finitely many closed affine
halfplanes, with nonempty interiors. Their interiors are pairwise disjoint and
their union is exactly the constructed source disk. No polygonality hypothesis
is imposed on the metric completion or on the original cut locus.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

open AffineArrangement

theorem exists_finite_source_polygon_cover :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      ∃ L : Set (Plane →ᵃ[ℝ] ℝ), L.Finite ∧ (∀ l ∈ L, l ≠ 0) ∧
        ∃ S : Set (L → Bool), S.Finite ∧
          (∀ signs ∈ S, IsCompact (closedChamber (fun l : L => l.val) signs) ∧
            Convex ℝ (closedChamber (fun l : L => l.val) signs) ∧
            (interior (closedChamber (fun l : L => l.val) signs)).Nonempty) ∧
          S.Pairwise (fun a b => Disjoint
            (interior (closedChamber (fun l : L => l.val) a))
            (interior (closedChamber (fun l : L => l.val) b))) ∧
          R.domain = ⋃ signs ∈ S, closedChamber (fun l : L => l.val) signs := by
  let := P.metricSpace
  intro source R
  obtain ⟨L, finite, nonzero, boundary⟩ := P.exists_finite_source_boundary_equations R
  let := finite.fintype
  let equations (l : L) := l.val
  have support : ∀ x ∈ frontier R.domain, ∃ l : L, equations l x = 0 := by
    intro x hx
    obtain ⟨l, hl, zero⟩ := boundary x hx
    exact ⟨⟨l, hl⟩, zero⟩
  obtain ⟨S, finite_S, pieces, cover⟩ := exists_finite_closed_chamber_cover equations
    (fun l => nonzero l.val l.property) R.compact_domain (P.sourceDomain_closure_interior R) support
  refine ⟨L, finite, nonzero, S, finite_S, ?_, ?_, cover⟩
  · intro signs member
    obtain ⟨nonempty, _, compact⟩ := pieces signs member
    exact ⟨compact, convex_closedChamber equations signs, by
      rw [interior_closedChamber equations signs nonempty]
      exact nonempty⟩
  · intro a ha b hb different
    rw [interior_closedChamber equations a (pieces a ha).1,
      interior_closedChamber equations b (pieces b hb).1]
    exact Set.disjoint_left.mpr (fun _ hx hy => different (chamber_signs_unique equations hx hy))

end Unfoldings.SpatialFolding.ConvexBoundary
