module

public import Unfoldings.Roof.CompletionMarkedPoints
public import Unfoldings.Cap.JordanContourPartition
public import Unfoldings.Geometry.RadialClosureContacts
public import Unfoldings.Roof.CompletedBankComparison

/-! Actual closure meshes with every closing corner retained in their intrinsic contour. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

universe u

variable {n : ℕ} (P : PolygonalChain Plane n) (q c : Plane)

/-- Both bank endpoints and both closing corners, with their geometric coordinates. -/
def closureMarkedPoint : Fin 4 → Plane := ![P.vertex 0, P.vertex (Fin.last n), q, c]

/-- Proper supporting lines for the curve and two crossing coordinate lines at every corner. -/
def markedClosureEquations : ULift.{u} ((Fin n ⊕ Fin 4) ⊕ (Fin 4 × Fin 2)) →
    Plane →ᵃ[ℝ] ℝ :=
  fun i => Sum.elim (P.closureEquations q c)
    (fun j => pointCoordinateEquation (P.closureMarkedPoint q c j.1) j.2) i.down

theorem markedClosureEquations_ne_zero
    (i : ULift.{u} ((Fin n ⊕ Fin 4) ⊕ (Fin 4 × Fin 2))) :
    P.markedClosureEquations q c i ≠ 0 := by
  rcases i with ⟨i⟩
  cases i with
  | inl j => exact P.closureEquations_ne_zero q c j
  | inr j => exact pointCoordinateEquation_ne_zero _ _

theorem markedClosureEquations_support (p : Plane)
    (member : p ∈ P.threeSegmentClosure q c) :
    ∃ i : ULift.{u} ((Fin n ⊕ Fin 4) ⊕ (Fin 4 × Fin 2)),
      P.markedClosureEquations q c i p = 0 := by
  obtain ⟨i, zero⟩ := P.closureEquations_support q c p member
  exact ⟨ULift.up (.inl i), zero⟩

theorem closureMarkedPoint_mem_curve (j : Fin 4) :
    P.closureMarkedPoint q c j ∈ P.threeSegmentClosure q c := by
  fin_cases j
  · exact Or.inl ⟨0, P.path.source⟩
  · exact Or.inl ⟨1, P.path.target⟩
  · exact Or.inr (Or.inr (left_mem_segment ℝ _ _))
  · exact Or.inr (Or.inl (Or.inl (right_mem_segment ℝ _ _)))

end Unfoldings.PolygonalChain

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

local instance {φ : ℝ} {region : Set Plane} {J : Type u}
    {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra) :
    Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

open Classical in
/-- Construct the physical completion and its actual contour corner occurrences.
No contour membership, traversal order or development is supplied. -/
theorem exists_marked_closure_completion {φ : ℝ} (positive : 0 < φ)
    (small : φ < Real.pi / 2) {n : ℕ} (P : PolygonalChain Plane n) (q c : Plane)
    (jordan : Schoenflies.IsJordanCurve (P.threeSegmentClosure q c)) :
    ∃ E : K.CompletionMesh φ (PlanarTopology.closedJordanDomain
        (P.threeSegmentClosure q c)) (P.markedClosureEquations q c),
      (∀ p ∈ PlanarTopology.closedJordanDomain (P.threeSegmentClosure q c),
        SpatialEnvelope.height (K.completionPlanes E.tentHeight (Real.sin φ / 2)) p =
          K.roofHeight p) ∧
      ∃ (contained : P.threeSegmentClosure q c ⊆ interior E.cap.footprint)
        (avoids : ∀ f, Disjoint (interior (E.cap.projectedTriangle f).carrier)
          (P.threeSegmentClosure q c)),
        ∀ j : Fin 4, ∃ i, E.cap.jordanBankPosition jordan
          (contained.trans interior_subset) avoids i = P.closureMarkedPoint q c j := by
  obtain ⟨E, preserved⟩ := K.exists_completionMesh_preserving_region positive small
    (PlanarTopology.isCompact_closedJordanDomain jordan) (P.markedClosureEquations q c)
    (P.markedClosureEquations_ne_zero q c)
  have curve_in_filling : P.threeSegmentClosure q c ⊆
      PlanarTopology.closedJordanDomain (P.threeSegmentClosure q c) := by
    intro p member
    rw [← PlanarTopology.frontier_closedJordanDomain jordan] at member
    exact (closure_eq_iff_isClosed.mpr isClosed_closure).subset
      (frontier_subset_closure member)
  have contained := curve_in_filling.trans E.region_inside
  have avoids := E.cap_avoids_supported_curve (P.markedClosureEquations_ne_zero q c)
    (P.markedClosureEquations_support q c)
  refine ⟨E, preserved, contained, avoids, ?_⟩
  intro j
  obtain ⟨w, at_point⟩ := E.exists_projected_vertex_of_coordinate_constraints
    (P.closureMarkedPoint q c j) (fun k => ULift.up (.inr (j, k))) (fun _ => rfl)
    (curve_in_filling (P.closureMarkedPoint_mem_curve q c j))
  obtain ⟨i, equal⟩ := E.cap.exists_jordanBankPosition_of_projected_vertex jordan
    (contained.trans interior_subset) avoids w
    (at_point ▸ P.closureMarkedPoint_mem_curve q c j)
  exact ⟨i, equal.trans at_point⟩

end Unfoldings.ConvexRoof
