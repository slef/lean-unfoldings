module

public import Unfoldings.Roof.MarkedContourPartition
public import Unfoldings.Cap.RadialCyclicBankComparison
public import Unfoldings.Cap.SmallBankRolling

/-! Uniform actual bank rolling on every physical marked completion, allowing extra refinements. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

local instance markedRollingIndexFintype {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
    {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra) :
    Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

open Classical in
/-- One positive tilt controls the actual rolling on every marked completion mesh.
The estimate survives imposition of additional physical cut constraints. -/
theorem exists_uniform_marked_completion_rolling {η : ℝ} (positive : 0 < η) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
        K.TiltBound φ → ∀ {n : ℕ} (P : PolygonalChain Plane n) (q c : Plane)
          (jordan : Schoenflies.IsJordanCurve (P.threeSegmentClosure q c)),
          P.RadialFrom q 0 → 0 < dist q (P.vertex 0) →
          dist q (P.vertex 0) < dist q (P.vertex (Fin.last n)) →
          ∀ (height : Plane →ₗ[ℝ] ℝ),
            (∀ z ∈ Set.range P.path, 0 ≤ height (z - q)) → height (c - q) < 0 →
            0 < inner ℝ (P.vertex (Fin.last n) - q) (c - P.vertex (Fin.last n)) →
            ∀ E : K.CompletionMesh φ (PlanarTopology.closedJordanDomain
                (P.threeSegmentClosure q c)) (P.markedClosureEquations q c),
              E.cap.HasSmallRadialBankRolling P q c jordan η := by
  obtain ⟨φ, bounds, budget⟩ := ConvexCap.exists_uniform_tilt_radial_bank_budget.{0, 0} positive
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt n P q c jordan radial initial progress height supported outside outward E
  have contained := E.markedClosure_inside P q c jordan
  have avoids := E.markedClosure_avoids P q c
  have cap_tilt := CompletionMesh.cap_tilt (E := E) bounds.1 bounds.2 tilt
  obtain ⟨corner, total⟩ := budget E.cap cap_tilt
  obtain ⟨first, last, ends_eq, on_first, off_last, estimate⟩ :=
    E.cap.exists_radial_bank_rolling_comparison P q c jordan (contained.trans interior_subset)
      avoids contained radial initial progress height supported outside outward
      (E.markedClosure_corner_occurs P q c jordan 0)
      (E.markedClosure_corner_occurs P q c jordan 1)
      (show 0 ≤ η / (32 * Real.pi) by positivity) corner bounds.1.le bounds.2 cap_tilt
  exact ⟨contained, avoids, first, last, ends_eq, on_first, off_last, estimate.trans_lt total⟩

end Unfoldings.ConvexRoof
