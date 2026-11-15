module

public import Unfoldings.Roof.MarkedClosureCompletion
public import Unfoldings.Cap.RadialCyclicBankComparison

/-! Construct uniformly accurate actual intrinsic bank rolling on physical roof completions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

local instance {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
    {K : ConvexRoof C} {φ : ℝ} {region : Set Plane} {J : Type u}
    {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra) :
    Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

open Classical in
/-- One tilt works before the roof, closure and physical mesh are supplied. The actual
completion, endpoint copies, bank orientation and unreduced rolling bound are constructed. -/
theorem exists_uniform_completed_bank_rolling {η : ℝ} (positive : 0 < η) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
        K.TiltBound φ → ∀ {n : ℕ} (P : PolygonalChain Plane n) (q c : Plane)
          (jordan : Schoenflies.IsJordanCurve (P.threeSegmentClosure q c)),
          P.RadialFrom q 0 → 0 < dist q (P.vertex 0) →
          dist q (P.vertex 0) < dist q (P.vertex (Fin.last n)) →
          ∀ (height : Plane →ₗ[ℝ] ℝ),
            (∀ z ∈ Set.range P.path, 0 ≤ height (z - q)) → height (c - q) < 0 →
            0 < inner ℝ (P.vertex (Fin.last n) - q) (c - P.vertex (Fin.last n)) →
            ∃ E : K.CompletionMesh φ (PlanarTopology.closedJordanDomain
                (P.threeSegmentClosure q c)) (P.markedClosureEquations q c),
              (∀ p ∈ PlanarTopology.closedJordanDomain (P.threeSegmentClosure q c),
                SpatialEnvelope.height (K.completionPlanes E.tentHeight (Real.sin φ / 2)) p =
                  K.roofHeight p) ∧
              ∃ (contained : P.threeSegmentClosure q c ⊆ interior E.cap.footprint)
                (avoids : ∀ f, Disjoint (interior (E.cap.projectedTriangle f).carrier)
                  (P.threeSegmentClosure q c)),
                ∃ first last : Fin ((E.cap.jordanContour jordan
                    (contained.trans interior_subset) avoids).length + 1),
                  ({E.cap.jordanBankPosition jordan (contained.trans interior_subset) avoids first,
                    E.cap.jordanBankPosition jordan (contained.trans interior_subset) avoids last} :
                      Finset Plane) = {P.vertex 0, P.vertex (Fin.last n)} ∧
                  E.cap.jordanContourBankOn jordan (contained.trans interior_subset) avoids
                    (Set.range P.path) first ∧
                  ¬ E.cap.jordanContourBankOn jordan (contained.trans interior_subset) avoids
                    (Set.range P.path) last ∧
                  |E.cap.jordanCyclicRollHeadingError jordan (contained.trans interior_subset)
                    avoids first ⟨((finCycle first).symm last).val - 1, by omega⟩| < η := by
  obtain ⟨φ, bounds, budget⟩ := ConvexCap.exists_uniform_tilt_radial_bank_budget.{0, 0} positive
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt n P q c jordan radial initial progress height supported outside outward
  obtain ⟨E, preserved, contained, avoids, marked⟩ :=
    K.exists_marked_closure_completion bounds.1 bounds.2 P q c jordan
  have cap_tilt := CompletionMesh.cap_tilt (E := E) bounds.1 bounds.2 tilt
  obtain ⟨corner, total⟩ := budget E.cap cap_tilt
  obtain ⟨first, last, ends_eq, on_first, off_last, estimate⟩ :=
    E.cap.exists_radial_bank_rolling_comparison P q c jordan (contained.trans interior_subset)
      avoids contained radial initial progress height supported outside outward
      (marked 0) (marked 1)
      (show 0 ≤ η / (32 * Real.pi) by positivity) corner bounds.1.le bounds.2 cap_tilt
  exact ⟨E, preserved, contained, avoids, first, last, ends_eq, on_first, off_last,
    estimate.trans_lt total⟩

end Unfoldings.ConvexRoof
