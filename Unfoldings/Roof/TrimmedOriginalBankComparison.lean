module

public import Unfoldings.Roof.CompletionOriginalBankWindowTrace
public import Unfoldings.Cap.UnconditionalOriginalBankHeadingComparison
public import Unfoldings.Roof.CompletionCombinedConstraints

/-! Uniform original real-heading comparison on constructed actual trimmed bank windows. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

local instance trimmedBankComparisonIndexFintype {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
    {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra) :
    Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

open Classical in
/-- Original supported radial trim geometry constructs an actual physical bank window
with a uniformly small error for the whole original real terminal heading. The source
may be perturbed away from the controlling radial source. All fine indices, original
cut copies, complete carrier matches, radial tests and selected-side alternatives are derived. -/
theorem exists_uniform_trimmed_original_bank_comparison {η : ℝ} (positive : 0 < η) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
        K.TiltBound φ → ∀ (retain : Set C.Seam) {n : ℕ}
          (coarse : (C.boundarySystem retain).Chain (n + 1))
          (cut : ∀ i, ¬ C.IsBoundaryEdge Set.univ (C.germEdge (coarse.point i).val))
          (control : Plane), (K.folding.projectedBoundaryChain coarse).RadialFrom control 0 →
          ∀ (a b : unitInterval) (first_before : a.val < 1)
            (_last_positive : 0 < b.val) (last_before : b.val < 1) (source closing : Plane),
            let P := (K.folding.projectedBoundaryChain coarse).trimEnds a b
            P.RadialFrom source 0 → 0 < dist source (P.vertex 0) →
            ∀ (height : Plane →ₗ[ℝ] ℝ),
              (∀ z ∈ Set.range P.path, 0 ≤ height (z - source)) → height (closing - source) < 0 →
              0 < inner ℝ (P.vertex (Fin.last (n + 2)) - source)
                (closing - P.vertex (Fin.last (n + 2))) →
              ∀ jordan : Schoenflies.IsJordanCurve (P.threeSegmentClosure source closing),
                ∃ E : K.CompletionMesh φ
                    (PlanarTopology.closedJordanDomain (P.threeSegmentClosure source closing))
                    (K.combinedCompletionEquations (P.markedClosureEquations source closing)),
                  (∀ p ∈ PlanarTopology.closedJordanDomain (P.threeSegmentClosure source closing),
                    SpatialEnvelope.height (K.completionPlanes E.tentHeight (Real.sin φ / 2)) p =
                      K.roofHeight p) ∧
                  let window := CompletionMesh.markedOriginalBankWindow coarse cut a b
                    source closing first_before last_before jordan E
                  |C.boundaryChainRollHeading coarse (Fin.last (n + 1)) -
                    E.cap.projectedFanRollHeading E.originalConstraintView.originalPieceSet
                      window.chain (Fin.last window.length)| < η := by
  obtain ⟨φ, bounds, uniform⟩ :=
    ConvexCap.exists_uniform_tilt_original_bank_heading_error_lt_unconditional.{0, 0} positive
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt retain n coarse cut control radial a b first_before last_positive
    last_before source closing
  dsimp only
  intro trim_radial initial height supported excluded outward jordan
  let P := (K.folding.projectedBoundaryChain coarse).trimEnds a b
  obtain ⟨E, preserved⟩ := K.exists_combined_completion (P.markedClosureEquations source closing)
    bounds.1 bounds.2 (PlanarTopology.isCompact_closedJordanDomain jordan)
    (P.markedClosureEquations_ne_zero source closing)
  let view := E.originalConstraintView
  let window := CompletionMesh.markedOriginalBankWindow coarse cut a b source closing
    first_before last_before jordan E
  have trace := window.cap_projected_trace_eq_trim control radial
  have closure := window.cap_projected_closure_eq_trim control radial source closing
  have first := window.cap_projected_initial.trans
    ((K.folding.projectedBoundaryChain coarse).trimEnds_start a b).symm
  have last := window.cap_projected_terminal.trans
    ((K.folding.projectedBoundaryChain coarse).trimEnds_last a b).symm
  have refined_initial := Eq.mpr (congrArg (fun p : Plane => 0 < dist source p) first) initial
  have refined_supported : ∀ z ∈
      Set.range (view.cap.projectedBoundaryChain view.originalPieceSet window.chain).path,
      0 ≤ height (z - source) := fun z member => supported z (trace.subset member)
  have refined_outward := Eq.mpr
    (congrArg (fun p : Plane => 0 < inner ℝ (p - source) (closing - p)) last) outward
  have refined_jordan := Eq.mpr (congrArg Schoenflies.IsJordanCurve closure) jordan
  have inside := E.extraConstraintView.markedClosure_inside P source closing jordan
  have avoids := E.extraConstraintView.markedClosure_avoids P source closing
  have refined_inside :
      (view.cap.projectedBoundaryChain view.originalPieceSet window.chain).threeSegmentClosure
        source closing ⊆ interior view.cap.footprint :=
    fun _ member => inside (closure.subset member)
  have refined_avoids : ∀ f, Disjoint (interior (view.cap.projectedTriangle f).carrier)
      ((view.cap.projectedBoundaryChain view.originalPieceSet window.chain).threeSegmentClosure
        source closing) := fun f => (avoids f).mono_right closure.subset
  have estimate := uniform E.cap (CompletionMesh.cap_tilt bounds.1 bounds.2 tilt)
    view.originalPieceSet window.chain source closing
    (window.cap_projected_radialFrom_trim control radial source trim_radial)
    refined_initial height refined_supported excluded refined_outward refined_jordan
    refined_inside refined_avoids
  have actual := (congrArg (fun heading : ℝ => |heading - E.cap.projectedFanRollHeading
    view.originalPieceSet window.chain (Fin.last window.length)|)
      (window.terminal_heading_eq last_positive).symm).trans_lt estimate
  exact ⟨E, preserved, actual⟩

end Unfoldings.ConvexRoof
