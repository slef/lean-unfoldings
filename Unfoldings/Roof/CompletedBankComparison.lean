module

public import Unfoldings.Roof.CompletionCurve
public import Unfoldings.Cap.RadialBankThreshold

/-! Uniform bank comparison on a constructed cap preserving the whole Jordan filling. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

universe u

variable {n : ℕ} (P : PolygonalChain Plane n) (q c : Plane)

/-- Lift the actual finite closing equations to the support family's universe. -/
def completionEquations : ULift.{u} (Fin n ⊕ Fin 4) → Plane →ᵃ[ℝ] ℝ :=
  fun i => P.closureEquations q c i.down

theorem completionEquations_ne_zero (i : ULift.{u} (Fin n ⊕ Fin 4)) :
    P.completionEquations q c i ≠ 0 := P.closureEquations_ne_zero q c i.down

theorem completionEquations_support (p : Plane) (member : p ∈ P.threeSegmentClosure q c) :
    ∃ i : ULift.{u} (Fin n ⊕ Fin 4), P.completionEquations q c i p = 0 := by
  obtain ⟨i, zero⟩ := P.closureEquations_support q c p member
  exact ⟨ULift.up i, zero⟩

end Unfoldings.PolygonalChain

namespace Unfoldings.ConvexRoof

universe u v

local instance {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
    {K : ConvexRoof C} {φ : ℝ} {region : Set Plane} {J : Type u}
    {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra) :
    Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

open Classical in
/-- One small tilt works for every roof and supported radial closure. The physical completion
and its curve avoidance are constructed, and its heights agree throughout the Jordan filling. -/
theorem exists_uniform_completed_bank_tilt {η : ℝ} (positive : 0 < η) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
        K.TiltBound φ → ∀ {n : ℕ} (P : PolygonalChain Plane n) (q c : Plane)
          (jordan : Schoenflies.IsJordanCurve (P.threeSegmentClosure q c)),
          0 < dist q (P.vertex 0) →
          dist q (P.vertex 0) < dist q (P.vertex (Fin.last n)) →
          ∀ (height : Plane →ₗ[ℝ] ℝ), 0 ≤ height (P.vertex 0 - q) →
            0 ≤ height (P.vertex (Fin.last n) - q) → height (c - q) < 0 →
            0 < inner ℝ (P.vertex (Fin.last n) - q) (c - P.vertex (Fin.last n)) →
            ∃ E : K.CompletionMesh φ (PlanarTopology.closedJordanDomain
                (P.threeSegmentClosure q c)) (P.completionEquations q c),
              (∀ p ∈ PlanarTopology.closedJordanDomain (P.threeSegmentClosure q c),
                SpatialEnvelope.height (K.completionPlanes E.tentHeight (Real.sin φ / 2)) p =
                  K.roofHeight p) ∧
              ∃ (contained : P.threeSegmentClosure q c ⊆ interior E.cap.footprint)
                (avoids : ∀ f, Disjoint (interior (E.cap.projectedTriangle f).carrier)
                  (P.threeSegmentClosure q c)),
                |∑ i ∈ E.cap.jordanGeometricBankIndices jordan (contained.trans interior_subset)
                    avoids (Set.range P.path)
                    (radialClosingCorners q (P.vertex 0) (P.vertex (Fin.last n)) c),
                  E.cap.jordanContourTurnError jordan (contained.trans interior_subset)
                    avoids i| < η := by
  obtain ⟨φ, bounds, budget⟩ := ConvexCap.exists_uniform_tilt_radial_bank_turn_error_lt.{0, 0}
    positive
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt n P q c jordan initial progress height first last outside outward
  obtain ⟨E, preserved⟩ := K.exists_completionMesh_preserving_region bounds.1 bounds.2
    (PlanarTopology.isCompact_closedJordanDomain jordan) (P.completionEquations q c)
    (P.completionEquations_ne_zero q c)
  have curve_in_filling : P.threeSegmentClosure q c ⊆
      PlanarTopology.closedJordanDomain (P.threeSegmentClosure q c) := by
    intro p member
    rw [← PlanarTopology.frontier_closedJordanDomain jordan] at member
    exact (closure_eq_iff_isClosed.mpr isClosed_closure).subset
      (frontier_subset_closure member)
  have contained := curve_in_filling.trans E.region_inside
  have avoids := E.cap_avoids_supported_curve (P.completionEquations_ne_zero q c)
    (P.completionEquations_support q c)
  exact ⟨E, preserved, contained, avoids,
    budget E.cap (CompletionMesh.cap_tilt bounds.1 bounds.2 tilt) P q c jordan contained avoids
      initial progress height first last outside outward⟩

end Unfoldings.ConvexRoof
