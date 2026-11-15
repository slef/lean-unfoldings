module

public import Unfoldings.Roof.MarkedClosureCompletion

/-! Geometric bank correspondence for actual marked physical completion contours. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {n : ℕ} (P : PolygonalChain Plane n) (q c : Plane)
  (E : K.CompletionMesh φ (PlanarTopology.closedJordanDomain
    (P.threeSegmentClosure q c)) (P.markedClosureEquations q c))
  (jordan : Schoenflies.IsJordanCurve (P.threeSegmentClosure q c))

local instance : Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

include jordan in
/-- The entire curve lies strictly inside its actual marked completion cap. -/
theorem markedClosure_inside : P.threeSegmentClosure q c ⊆ interior E.cap.footprint := by
  apply Set.Subset.trans _ E.region_inside
  intro p member
  rw [← PlanarTopology.frontier_closedJordanDomain jordan] at member
  exact (closure_eq_iff_isClosed.mpr isClosed_closure).subset
    (frontier_subset_closure member)

/-- Actual line constraints make the completion respect the whole curve. -/
theorem markedClosure_avoids (i : E.mesh.Index) :
    Disjoint (interior (E.cap.projectedTriangle i).carrier) (P.threeSegmentClosure q c) :=
  E.cap_avoids_supported_curve (P.markedClosureEquations_ne_zero q c)
    (P.markedClosureEquations_support q c) i

include jordan in
open Classical in
/-- The physical marked constraints construct the corner's actual contour occurrence. -/
theorem markedClosure_corner_occurs (j : Fin 4) :
    ∃ i, E.cap.jordanBankPosition jordan
      ((E.markedClosure_inside P q c jordan).trans interior_subset)
      (E.markedClosure_avoids P q c) i = P.closureMarkedPoint q c j := by
  have on_curve := P.closureMarkedPoint_mem_curve q c j
  have in_filling : P.closureMarkedPoint q c j ∈
      PlanarTopology.closedJordanDomain (P.threeSegmentClosure q c) := by
    rw [← PlanarTopology.frontier_closedJordanDomain jordan] at on_curve
    exact (closure_eq_iff_isClosed.mpr isClosed_closure).subset
      (frontier_subset_closure on_curve)
  obtain ⟨w, at_point⟩ := E.exists_projected_vertex_of_coordinate_constraints
    (P.closureMarkedPoint q c j) (fun k => ULift.up (.inr (j, k))) (fun _ => rfl) in_filling
  obtain ⟨i, equal⟩ := E.cap.exists_jordanBankPosition_of_projected_vertex jordan
    ((E.markedClosure_inside P q c jordan).trans interior_subset)
    (E.markedClosure_avoids P q c) w (at_point ▸ on_curve)
  exact ⟨i, equal.trans at_point⟩

include jordan in
open Classical in
/-- Every actual contour bank belongs wholly to the prescribed radial bank or one closing link.
This correspondence is derived from the physical mesh and radial geometry. -/
theorem markedClosure_contour_piece (radial : P.RadialFrom q 0)
    (initial : 0 < dist q (P.vertex 0))
    (progress : dist q (P.vertex 0) < dist q (P.vertex (Fin.last n)))
    (height : Plane →ₗ[ℝ] ℝ) (supported : ∀ z ∈ Set.range P.path, 0 ≤ height (z - q))
    (outside : height (c - q) < 0)
    (outward : 0 < inner ℝ (P.vertex (Fin.last n) - q) (c - P.vertex (Fin.last n)))
    (i : Fin ((E.cap.jordanContour jordan
      ((E.markedClosure_inside P q c jordan).trans interior_subset)
      (E.markedClosure_avoids P q c)).length + 1)) :
    ∃ j : Fin 4, segment ℝ
      (E.cap.jordanBankPosition jordan
        ((E.markedClosure_inside P q c jordan).trans interior_subset)
        (E.markedClosure_avoids P q c) i)
      (E.cap.jordanBankPosition jordan
        ((E.markedClosure_inside P q c jordan).trans interior_subset)
        (E.markedClosure_avoids P q c) (finRotate _ i)) ⊆ P.radialClosurePieces q c j := by
  let pos := E.cap.jordanBankPosition jordan
    ((E.markedClosure_inside P q c jordan).trans interior_subset) (E.markedClosure_avoids P q c)
  have marked (j : Fin 4) : P.closureMarkedPoint q c j ∈ Set.range pos :=
    E.markedClosure_corner_occurs P q c jordan j
  have corners : (radialClosingCorners q (P.vertex 0) (P.vertex (Fin.last n)) c : Set Plane) ⊆
      Set.range pos := by
    intro z member
    simp only [radialClosingCorners, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact marked 0
    · exact marked 1
    · exact marked 2
    · exact marked 3
  exact E.cap.jordanContour_segment_subset_piece jordan
    ((E.markedClosure_inside P q c jordan).trans interior_subset) (E.markedClosure_avoids P q c)
    (P.radialClosurePieces q c) (P.radialClosurePieces_closed q c)
    (P.threeSegmentClosure_subset_pieces q c)
    (fun j k different => (P.radialClosurePieces_contacts q c radial initial progress height
      supported outside outward j k different).trans corners) i

end Unfoldings.ConvexRoof.CompletionMesh
