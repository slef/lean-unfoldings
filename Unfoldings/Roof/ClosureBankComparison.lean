module

public import Unfoldings.Roof.PolygonalClosureMesh
public import Unfoldings.Cap.RadialBankThreshold

/-! Actual small bank error on the physically constructed closure-respecting cap refinement. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
  (T : Triangulation family Z) {n : ℕ} (P : PolygonalChain Plane n) (q c : Plane)
  (inside : (interior (clip family Z)).Nonempty)

local instance closureBankIndexFintype : Fintype (T.alignToClosure P q c inside).Index :=
  @Fintype.ofFinite _ (T.alignToClosure P q c inside).finite

/-- The actual line-respecting physical mesh inherits the original support-plane tilt. -/
theorem closureCap_tilt {φ : ℝ} (height : ∀ i : I, Real.cos φ ≤ (family i).normal 2) :
    (T.closureCap P q c inside).TiltBound φ :=
  (T.alignToClosure P q c inside).toTriangulation.normalizedCap_tilt
    (T.alignToClosure_conforming P q c inside) inside height

open Classical in
/-- One positive tilt controls every actual closure mesh, before its input is supplied. -/
theorem exists_uniform_closure_bank_tilt {η : ℝ} (positive : 0 < η) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
        (T : Triangulation family Z) {n : ℕ} (P : PolygonalChain Plane n) (q c : Plane)
        (inside : (interior (clip family Z)).Nonempty),
        (∀ i : I, Real.cos φ ≤ (family i).normal 2) →
        ∀ (jordan : Schoenflies.IsJordanCurve (P.threeSegmentClosure q c))
          (contained : P.threeSegmentClosure q c ⊆ interior (clip family Z)),
          0 < dist q (P.vertex 0) →
          dist q (P.vertex 0) < dist q (P.vertex (Fin.last n)) →
          ∀ (height : Plane →ₗ[ℝ] ℝ), 0 ≤ height (P.vertex 0 - q) →
            0 ≤ height (P.vertex (Fin.last n) - q) → height (c - q) < 0 →
            0 < inner ℝ (P.vertex (Fin.last n) - q) (c - P.vertex (Fin.last n)) →
            let K := T.closureCap P q c inside
            let containment : P.threeSegmentClosure q c ⊆ interior K.footprint := by
              rwa [T.closureCap_footprint]
            let avoids := T.closureCap_avoids P q c inside
            |∑ i ∈ K.jordanGeometricBankIndices jordan (containment.trans interior_subset) avoids
                (Set.range P.path)
                (radialClosingCorners q (P.vertex 0) (P.vertex (Fin.last n)) c),
              K.jordanContourTurnError jordan (containment.trans interior_subset)
                avoids i| < η := by
  obtain ⟨φ, bounds, budget⟩ := ConvexCap.exists_uniform_tilt_radial_bank_budget.{0, 0} positive
  refine ⟨φ, bounds, ?_⟩
  intro I _ _ family Z T n P q c inside tilt jordan contained initial progress height first last
    outside outward
  dsimp only
  let K := T.closureCap P q c inside
  have cap_tilt := T.closureCap_tilt P q c inside tilt
  obtain ⟨corner, total⟩ := budget K cap_tilt
  exact (K.abs_radial_bank_turn_error_le P q c jordan
    (by rw [T.closureCap_footprint]; exact contained.trans interior_subset)
    (T.closureCap_avoids P q c inside) (by rwa [T.closureCap_footprint]) initial progress height
    first last outside outward (by positivity) corner bounds.1.le bounds.2 cap_tilt).trans_lt total

end Unfoldings.SpatialEnvelope.Triangulation
