module

public import Unfoldings.Roof.ShortWindowRolling
public import Unfoldings.Geometry.PolarWindowRadial

/-! The weighted heading argument's exact polar windows construct actual bank comparisons. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

local instance polarWindowRollingIndexFintype {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
    {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra) :
    Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

open Classical in
/-- The same strict polar window used in the weighted estimates supplies the whole physical
comparison, including actual intrinsic rolling and original-cut metric preservation. -/
theorem exists_uniform_polar_window_rolling {η : ℝ} (positive : 0 < η) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
        K.TiltBound φ → ∀ {n m : ℕ} (P : PolygonalChain ℂ n) (source : ℂ),
          (∀ i, P.vertex i - source ≠ 0) → (∀ i, P.edge i ≠ 0) →
          (∀ i, P.edge i ≠ 0 → 0 < inner ℝ (P.vertex i.castSucc - source) (P.edge i)) →
          ∀ (first : ℕ) (fits : first + (m + 2) ≤ n),
            interiorVariation (P.polarVariation source) ⟨first, by omega⟩
              ⟨first + m + 1, by omega⟩ < Real.pi / 4 →
            let Q := P.planarWindow first fits
            let q := Complex.orthonormalBasisOneI.repr source
            ∃ a b : unitInterval, (0 < a.val ∧ a.val < 1) ∧ (0 < b.val ∧ b.val < 1) ∧
              ∃ (c : Plane)
                (jordan : Schoenflies.IsJordanCurve ((Q.trimEnds a b).threeSegmentClosure q c)),
                ∃ E : K.CompletionMesh φ (PlanarTopology.closedJordanDomain
                    ((Q.trimEnds a b).threeSegmentClosure q c))
                    (K.combinedCompletionEquations ((Q.trimEnds a b).markedClosureEquations q c)),
                  (∀ p ∈ PlanarTopology.closedJordanDomain
                      ((Q.trimEnds a b).threeSegmentClosure q c),
                    SpatialEnvelope.height (K.completionPlanes E.tentHeight (Real.sin φ / 2)) p =
                      K.roofHeight p) ∧
                  E.cap.HasSmallRadialBankRolling (Q.trimEnds a b) q c jordan η := by
  obtain ⟨φ, bounds, control⟩ := exists_uniform_short_window_rolling.{u, v} positive
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt n m P source genuine nonzero progress first fits small
  dsimp only
  apply control K tilt (P.planarWindow first fits) (Complex.orthonormalBasisOneI.repr source)
    (P.planarWindow_strictRadialSource source first fits progress)
    (P.planarWindow_initial_dist_pos source first fits genuine)
    (P.planarWindow_edge_ne_zero first fits nonzero _)
    (P.planarWindow_internalSourceRay_ne_zero source first fits genuine)
  rwa [P.planarWindow_internal_angle_sum source genuine first fits]

end Unfoldings.ConvexRoof
