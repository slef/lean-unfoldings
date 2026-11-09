module

public import Unfoldings.Source.PolygonalPieces
public import Unfoldings.Geometry.ArrangementBoundary
public import Unfoldings.Geometry.CompactCollinear

/-!
# The source boundary is a finite union of actual straight segments

Inside/outside chamber intersections give an exact finite boundary cover.
Each nonempty intersection is a compact convex subset of a proper planar
line, hence a closed segment. Every whole segment inherits one original-face
rigid placement from its inside polygon.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

open AffineArrangement

theorem exists_finite_source_boundary_segments :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      ∃ edges : Set (Plane × Plane), edges.Finite ∧
        frontier R.domain = ⋃ e ∈ edges, segment ℝ e.1 e.2 ∧
        ∀ e ∈ edges, ∃ (f : Face) (A : Plane ≃ᵃⁱ[ℝ] Plane), ∀ z : R.domain,
          z.val ∈ segment ℝ e.1 e.2 → ∃ y : C.Cell f, z.val = A y.val ∧
            R.projection (P.sourcePathCoordinate_injective R) z = C.faceMap Set.univ f y := by
  let := P.metricSpace
  intro source R
  obtain ⟨L, finite_L, nonzero, S, finite_S, polygons, _, cover⟩ :=
    P.exists_finite_source_polygon_pieces R
  let := finite_L.fintype
  let equations (l : L) := l.val
  have included (a : L → Bool) (member : a ∈ S) : closedChamber equations a ⊆ R.domain :=
    (polygons a member).2.2.2.1
  have support : ∀ x ∈ frontier R.domain, ∃ l : L, equations l x = 0 :=
    frontier_support_of_chamber_cover equations R.closed_domain S included cover
  obtain ⟨T, finite_T, boundary_cover, zero⟩ := exists_boundary_chamber_cover equations
    (fun l => nonzero l.val l.property) R.closed_domain support S included cover
  let := finite_S.fintype
  let := finite_T.fintype
  let region (p : S × T) := closedChamber equations p.1.val ∩ closedChamber equations p.2.val
  let J := {p : S × T // (region p).Nonempty}
  have segments (j : J) : ∃ a ∈ region j.val, ∃ b ∈ region j.val,
      region j.val = segment ℝ a b := by
    have compact := (polygons j.val.1.val j.val.1.property).1.inter_right
      (isClosed_closedChamber equations j.val.2.val)
    have convex := (convex_closedChamber equations j.val.1.val).inter
      (convex_closedChamber equations j.val.2.val)
    obtain ⟨l, vanishes⟩ := zero j.val.1.val j.val.1.property j.val.2.val j.val.2.property
    exact exists_segment_of_compact_convex_collinear compact convex j.property
      (collinear_of_affine_zero l.val (nonzero l.val l.property) vanishes)
  choose first member_first last member_last equal using segments
  let edges := Set.range (fun j : J => (first j, last j))
  have boundary_equal : frontier R.domain = ⋃ e ∈ edges, segment ℝ e.1 e.2 := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, body⟩ := Set.mem_iUnion₂.mp (boundary_cover ▸ hx)
      obtain ⟨b, hb, xa, xb⟩ := Set.mem_iUnion₂.mp body
      let j : J := ⟨(⟨a, ha⟩, ⟨b, hb⟩), ⟨x, xa, xb⟩⟩
      exact Set.mem_iUnion₂.mpr ⟨(first j, last j), ⟨j, rfl⟩,
        (Set.ext_iff.mp (equal j) x).mp ⟨xa, xb⟩⟩
    · intro hx
      obtain ⟨e, ⟨j, rfl⟩, point⟩ := Set.mem_iUnion₂.mp hx
      have in_region := (Set.ext_iff.mp (equal j) x).mpr point
      rw [boundary_cover]
      exact Set.mem_iUnion₂.mpr ⟨j.val.1.val, j.val.1.property,
        Set.mem_iUnion₂.mpr ⟨j.val.2.val, j.val.2.property, in_region⟩⟩
  refine ⟨edges, Set.finite_range _, boundary_equal, ?_⟩
  rintro e ⟨j, rfl⟩
  obtain ⟨f, A, formula⟩ := (polygons j.val.1.val j.val.1.property).2.2.2.2
  refine ⟨f, A, ?_⟩
  intro z hz
  exact formula z ((Set.ext_iff.mp (equal j) z.val).mpr hz).1

end Unfoldings.SpatialFolding.ConvexBoundary
