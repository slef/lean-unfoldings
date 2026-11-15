module

public import Unfoldings.Roof.MarkedCompletionRolling
public import Unfoldings.Roof.CompletionCombinedConstraints
public import Unfoldings.Geometry.RayWindowClosure

/-! Short radial windows construct physical comparison disks and accurate intrinsic rolling. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

local instance shortWindowIndexFintype {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
    {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra) :
    Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

open Classical in
/-- Short-window geometry alone constructs a uniformly accurate actual rolled bank.
The comparison respects original-face sides and preserves every original-cut metric. -/
theorem exists_uniform_short_window_rolling {η : ℝ} (positive : 0 < η) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
        K.TiltBound φ → ∀ {n : ℕ} (P : PolygonalChain Plane (n + 2)) (source : Plane),
          source ∈ P.strictRadialSources → 0 < dist source (P.vertex 0) →
          P.edge (Fin.last (n + 1)) ≠ 0 →
          (∀ i, P.internalSourceRay source i ≠ 0) →
          (∑ k : Fin n, InnerProductGeometry.angle
            (P.internalSourceRay source k.castSucc) (P.internalSourceRay source k.succ)) <
              Real.pi / 4 →
          ∃ a b : unitInterval, (0 < a.val ∧ a.val < 1) ∧ (0 < b.val ∧ b.val < 1) ∧
            ∃ (c : Plane)
              (jordan : Schoenflies.IsJordanCurve ((P.trimEnds a b).threeSegmentClosure source c)),
              ∃ E : K.CompletionMesh φ (PlanarTopology.closedJordanDomain
                  ((P.trimEnds a b).threeSegmentClosure source c))
                  (K.combinedCompletionEquations
                    ((P.trimEnds a b).markedClosureEquations source c)),
                (∀ p ∈ PlanarTopology.closedJordanDomain
                    ((P.trimEnds a b).threeSegmentClosure source c),
                  SpatialEnvelope.height (K.completionPlanes E.tentHeight (Real.sin φ / 2)) p =
                    K.roofHeight p) ∧
                E.cap.HasSmallRadialBankRolling (P.trimEnds a b) source c jordan η := by
  obtain ⟨φ, bounds, uniform⟩ := exists_uniform_marked_completion_rolling.{u, v} positive
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt n P source strict initial last_nonzero genuine small
  obtain ⟨a, b, first, last, c, height, trimmed_initial, progress, radial, supported,
      outside, outward, jordan⟩ :=
    P.exists_supported_ray_window_closure source strict initial last_nonzero genuine small
  let Q := P.trimEnds a b
  obtain ⟨E, preserved⟩ := K.exists_combined_completion (Q.markedClosureEquations source c)
    bounds.1 bounds.2 (PlanarTopology.isCompact_closedJordanDomain jordan)
    (Q.markedClosureEquations_ne_zero source c)
  have rolling := uniform K tilt Q source c jordan radial trimmed_initial progress height
    supported outside outward E.extraConstraintView
  exact ⟨a, b, first, last, c, jordan, E, preserved, rolling⟩

end Unfoldings.ConvexRoof
