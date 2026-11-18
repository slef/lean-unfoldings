module

public import Unfoldings.Roof.TrimmedOriginalBankComparison
public import Unfoldings.Roof.ProjectedBankDirections
public import Unfoldings.Geometry.SupportedRayWindowClosure

/-! Short actual cut-bank windows construct physical comparisons with real heading control. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

local instance supportedOriginalBankWindowIndexFintype {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
    {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra) :
    Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

open Classical in
/-- Every short source-ray window on an actual original cut-bank chain constructs
its generic trims, supported Jordan closure and respected physical cap. Its actual
intrinsic window retains every original real turn and has uniformly small real
heading error. No fine-bank, fan-angle, closure or source-perturbation certificate is supplied. -/
theorem exists_uniform_supported_original_bank_window {η : ℝ} (positive : 0 < η) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
        K.TiltBound φ → ∀ (retain : Set C.Seam) {n : ℕ}
          (coarse : (C.boundarySystem retain).Chain (n + 1))
          (cut : ∀ i, ¬ C.IsBoundaryEdge Set.univ (C.germEdge (coarse.point i).val)),
          let P := K.folding.projectedBoundaryChain coarse
          ∀ (control : Plane), control ∈ P.strictRadialSources →
            0 < dist control (P.vertex 0) →
            (∑ k : Fin n, InnerProductGeometry.angle
              (P.internalSourceRay control k.castSucc) (P.internalSourceRay control k.succ)) <
                Real.pi / 4 → ∀ {δ : ℝ}, 0 < δ →
            ∃ (a b : unitInterval) (first : 0 < a.val ∧ a.val < 1)
              (last : 0 < b.val ∧ b.val < 1), ∃ (q c : Plane) (height : Plane →ₗ[ℝ] ℝ),
              let Q := P.trimEnds a b
              dist q control < δ ∧ Q.RadialFrom q 0 ∧ 0 < dist q (Q.vertex 0) ∧
              (∀ z ∈ Set.range Q.path, 0 ≤ height (z - q)) ∧ height (c - q) < 0 ∧
              0 < inner ℝ (Q.vertex (Fin.last (n + 2)) - q)
                (c - Q.vertex (Fin.last (n + 2))) ∧
              ∃ jordan : Schoenflies.IsJordanCurve (Q.threeSegmentClosure q c),
                ∃ E : K.CompletionMesh φ
                    (PlanarTopology.closedJordanDomain (Q.threeSegmentClosure q c))
                    (K.combinedCompletionEquations (Q.markedClosureEquations q c)),
                  (∀ p ∈ PlanarTopology.closedJordanDomain (Q.threeSegmentClosure q c),
                    SpatialEnvelope.height (K.completionPlanes E.tentHeight (Real.sin φ / 2)) p =
                      K.roofHeight p) ∧
                  let window := CompletionMesh.markedOriginalBankWindow coarse cut a b q c
                    first.2 last.2 jordan E
                  |C.boundaryChainRollHeading coarse (Fin.last (n + 1)) -
                    E.cap.projectedFanRollHeading E.originalConstraintView.originalPieceSet
                      window.chain (Fin.last window.length)| < η := by
  obtain ⟨φ, bounds, uniform⟩ := exists_uniform_trimmed_original_bank_comparison.{u, v} positive
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt retain n coarse cut
  dsimp only
  intro control strict initial short δ room
  let P := K.folding.projectedBoundaryChain coarse
  have radial := P.radialFrom_of_strictRadialSource strict
  have genuine (j : Fin (n + 1)) : P.internalSourceRay control j ≠ 0 := by
    intro zero
    have same : P.vertex j.succ.castSucc = control := sub_eq_zero.mp zero
    have lower := (P.path_radius_bounds control radial (P.vertex_mem_path_range j.succ.castSucc)).1
    have positive_distance := initial.trans_le lower
    rw [same, dist_self] at positive_distance
    exact (lt_irrefl _ positive_distance)
  obtain ⟨a, b, first, last, q, c, height, nearby, trimmed_radial, trimmed_initial, _progress,
      supported, excluded, outward, _regular, _vertices, _first_link, _middle_link, _last_link,
      jordan⟩ := P.exists_supported_vertex_avoiding_ray_window_closure control strict initial
    (K.projectedBoundaryChain_edge_ne_zero coarse (Fin.last (n + 1))) genuine short
    K.projectedVertex K.originalEdgeEquations K.originalEdgeEquations_ne_zero room
  obtain ⟨E, preserved, estimate⟩ := uniform K tilt retain coarse cut control radial a b first.2
    last.1 last.2 q c trimmed_radial trimmed_initial height supported excluded outward jordan
  exact ⟨a, b, first, last, q, c, height, nearby, trimmed_radial, trimmed_initial, supported,
    excluded, outward, jordan, E, preserved, estimate⟩

end Unfoldings.ConvexRoof
