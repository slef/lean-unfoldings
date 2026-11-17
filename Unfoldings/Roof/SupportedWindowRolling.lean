module

public import Unfoldings.Roof.MarkedCompletionRolling
public import Unfoldings.Roof.CompletionCombinedConstraints
public import Unfoldings.Geometry.SupportedRayWindowClosure

/-! Generic supported comparison windows retain prescribed cuts and physical original fans. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v w

local instance supportedWindowRollingIndexFintype {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
    {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra) :
    Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

open Classical in
/-- One tilt constructs actual comparison caps for all short radial windows. The closing
links avoid prescribed vertices, the source moves arbitrarily little, and the same physical
completion respects prescribed cuts, original face sides and all marked closure lines. -/
theorem exists_uniform_supported_window_rolling {η : ℝ} (positive : 0 < η) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
        K.TiltBound φ → ∀ {n : ℕ} (P : PolygonalChain Plane (n + 2)) (source : Plane),
          source ∈ P.strictRadialSources → 0 < dist source (P.vertex 0) →
          P.edge (Fin.last (n + 1)) ≠ 0 →
          (∀ i, P.internalSourceRay source i ≠ 0) →
          (∑ k : Fin n, InnerProductGeometry.angle
            (P.internalSourceRay source k.castSucc) (P.internalSourceRay source k.succ)) <
              Real.pi / 4 →
          ∀ {ι : Type w} {κ : Type u} [Finite ι] [Finite κ]
            (point : ι → Plane) (equation : κ → Plane →ᵃ[ℝ] ℝ),
            (∀ j, equation j ≠ 0) → ∀ {δ : ℝ}, 0 < δ →
            ∃ a b : unitInterval, (0 < a.val ∧ a.val < 1) ∧ (0 < b.val ∧ b.val < 1) ∧
              ∃ (q c : Plane) (height : Plane →ₗ[ℝ] ℝ),
                let Q := P.trimEnds a b
                dist q source < δ ∧ Q.RadialFrom q 0 ∧
                0 < dist q (Q.vertex 0) ∧
                dist q (Q.vertex 0) < dist q (Q.vertex (Fin.last (n + 2))) ∧
                (∀ z ∈ Set.range Q.path, 0 ≤ height (z - q)) ∧ height (c - q) < 0 ∧
                0 < inner ℝ (Q.vertex (Fin.last (n + 2)) - q)
                  (c - Q.vertex (Fin.last (n + 2))) ∧
                (∀ j, equation j q ≠ 0 ∧ equation j c ≠ 0) ∧
                (∀ j, q ≠ point j ∧ c ≠ point j) ∧
                (∀ j, point j ∈ segment ℝ (Q.vertex 0) q → point j = Q.vertex 0) ∧
                (∀ j, point j ∉ segment ℝ q c) ∧
                (∀ j, point j ∈ segment ℝ (Q.vertex (Fin.last (n + 2))) c →
                  point j = Q.vertex (Fin.last (n + 2))) ∧
                ∃ jordan : Schoenflies.IsJordanCurve (Q.threeSegmentClosure q c),
                  ∃ E : K.CompletionMesh φ
                      (PlanarTopology.closedJordanDomain (Q.threeSegmentClosure q c))
                      (K.combinedCompletionEquations
                        (Sum.elim equation (Q.markedClosureEquations q c))),
                    (∀ p ∈ PlanarTopology.closedJordanDomain (Q.threeSegmentClosure q c),
                      SpatialEnvelope.height
                        (K.completionPlanes E.tentHeight (Real.sin φ / 2)) p = K.roofHeight p) ∧
                    E.cap.HasSmallRadialBankRolling Q q c jordan η := by
  obtain ⟨φ, bounds, uniform⟩ := exists_uniform_marked_completion_rolling.{u, v} positive
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt n P source strict initial last_nonzero genuine small
    ι κ _ _ point equation proper δ room
  obtain ⟨a, b, first, last, q, c, height, nearby, radial, trimmed_initial, progress,
    supported, outside, outward, regular, vertices, first_link, middle_link, last_link, jordan⟩ :=
    P.exists_supported_vertex_avoiding_ray_window_closure source strict initial last_nonzero
      genuine small point equation proper room
  let Q := P.trimEnds a b
  let extra := Sum.elim equation (Q.markedClosureEquations q c)
  have extra_proper : ∀ j, extra j ≠ 0 := by
    intro j
    cases j with
    | inl j => exact proper j
    | inr j => exact Q.markedClosureEquations_ne_zero q c j
  obtain ⟨E, preserved⟩ := K.exists_combined_completion extra bounds.1 bounds.2
    (PlanarTopology.isCompact_closedJordanDomain jordan) extra_proper
  let marked := E.extraConstraintView.selectConstraints (Q.markedClosureEquations q c)
    Sum.inr (fun _ => rfl)
  have rolling := uniform K tilt Q q c jordan radial trimmed_initial progress height supported
    outside outward marked
  exact ⟨a, b, first, last, q, c, height, nearby, radial, trimmed_initial, progress,
    supported, outside, outward, regular, vertices, first_link, middle_link, last_link,
    jordan, E, preserved, rolling⟩

end Unfoldings.ConvexRoof
