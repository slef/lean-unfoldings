module

public import Unfoldings.Geometry.ChamberTriangulation
public import Unfoldings.Geometry.AffineSupport
public import Unfoldings.Geometry.TriangleFrontier

/-!
# Triangle refinements respecting prescribed lines

Include every parent triangle's barycentric supporting lines and every extra
constraint line in one arrangement. Its compact chambers are triangulated
without crossing any constraint. Each resulting triangle lies in one whole
original parent, even when those original parents overlap.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {I J : Type} [Finite I] [Finite J]
  (original : I → Triangle) (extra : J → Plane →ᵃ[ℝ] ℝ)

def triangleRefinementEquations : (I × Fin 3) ⊕ J → Plane →ᵃ[ℝ] ℝ :=
  Sum.elim (fun i => (original i.1).coord i.2) extra

structure ConstrainedTriangleRefinement where
  Index : Type
  finite : Finite Index
  triangle : Index → Triangle
  parent : Index → I
  subset_parent : ∀ i, (triangle i).carrier ⊆ (original (parent i)).carrier
  signs : Index → J → Bool
  constrained : ∀ i, ∀ p ∈ (triangle i).carrier, ∀ j,
    0 ≤ AffineArrangement.signed (extra j) (signs i j) p
  cover : (⋃ i, (original i).carrier) = ⋃ i, (triangle i).carrier
  separated : Pairwise (fun i j =>
    Disjoint (interior (triangle i).carrier) (interior (triangle j).carrier))

/-- Construct a finite refinement subordinate to the old triangles and the supplied lines. -/
def constrainedTriangleRefinement (proper : ∀ j, extra j ≠ 0)
    (convex : Convex ℝ (⋃ i, (original i).carrier))
    (nonempty : (interior (⋃ i, (original i).carrier)).Nonempty) :
    ConstrainedTriangleRefinement original extra := Classical.choice (by
  let equation := triangleRefinementEquations original extra
  have proper_equation (j : (I × Fin 3) ⊕ J) : equation j ≠ 0 := by
    cases j with
    | inl j => exact (original j.1).coord_ne_zero j.2
    | inr j => exact proper j
  have compact : IsCompact (⋃ i, (original i).carrier) :=
    isCompact_iUnion (fun i => (original i).compact_carrier)
  have regular_closed : closure (interior (⋃ i, (original i).carrier)) =
      ⋃ i, (original i).carrier :=
    (convex.closure_interior_eq_closure_of_nonempty_interior nonempty).trans
      compact.isClosed.closure_eq
  have boundary : ∀ p ∈ frontier (⋃ i, (original i).carrier), ∃ j, equation j p = 0 := by
    intro p member
    obtain ⟨i, in_triangle⟩ := Set.mem_iUnion.mp (compact.isClosed.frontier_subset member)
    have on_frontier : p ∈ frontier (original i).carrier := by
      refine ⟨subset_closure in_triangle, fun inside => member.2 ?_⟩
      exact interior_mono (Set.subset_iUnion (fun j => (original j).carrier) i) inside
    obtain ⟨e, on_edge⟩ := Set.mem_iUnion.mp
      ((original i).frontier_eq_union_edges ▸ on_frontier)
    exact ⟨Sum.inl (i, Triangle.next (Triangle.next e)),
      (original i).coord_edge_eq_zero e ⟨p, on_edge⟩⟩
  obtain ⟨A, finite, triangle, signs, cover, separated, contained⟩ :=
    AffineArrangement.exists_finite_chamber_triangle_partition equation proper_equation compact
      regular_closed boundary
  have parents (a : A) : ∃ i, (triangle a).carrier ⊆ (original i).carrier := by
    obtain ⟨q, inside⟩ := (triangle a).interior_nonempty
    have in_union : q ∈ ⋃ i, (original i).carrier :=
      cover.symm ▸ Set.mem_iUnion.mpr ⟨a, interior_subset inside⟩
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp in_union
    have in_chamber : q ∈ AffineArrangement.chamber equation (signs a) := by
      rw [← AffineArrangement.interior_closedChamber equation (signs a) (contained a).1]
      exact interior_mono (contained a).2 inside
    refine ⟨i, fun p hp => (original i).carrier_eq_nonneg_coord.ge (fun k => ?_)⟩
    exact AffineArrangement.closedChamber_nonnegative_of_chamber_nonnegative equation (signs a)
      in_chamber ((contained a).2 hp) (Sum.inl (i, k))
        ((original i).carrier_eq_nonneg_coord.le member k)
  choose parent subset_parent using parents
  exact ⟨{ Index := A
           finite := finite
           triangle := triangle
           parent := parent
           subset_parent := subset_parent
           signs a j := signs a (Sum.inr j)
           constrained a p member j := (contained a).2 member (Sum.inr j)
           cover := cover
           separated := separated }⟩)

end Unfoldings
