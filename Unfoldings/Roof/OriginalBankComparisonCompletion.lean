module

public import Unfoldings.Roof.CompletionOriginalBankComparison
public import Unfoldings.Roof.CompletionChainClosure
public import Unfoldings.Roof.MarkedContourPartition
public import Unfoldings.Roof.CompletionCombinedConstraints

/-! Original bank geometry constructs respected physical completions with small real error. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

local instance originalBankCompletionIndexFintype {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
    {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra) :
    Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

open Classical in
/-- Original radial cut-bank geometry constructs a physical cap preserving the
whole roof over its Jordan comparison region, and bounds the original bank's
unreduced terminal heading against the actual projected fine fans. The mesh,
fine banks, radial refinement, closure matching and incident-side choice are all derived. -/
theorem exists_uniform_original_bank_comparison_completion {η : ℝ} (positive : 0 < η) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
        K.TiltBound φ → ∀ (retain : Set C.Seam) {n : ℕ}
          (coarse : (C.boundarySystem retain).Chain n)
          (cut : ∀ i, ¬ C.IsBoundaryEdge Set.univ (C.germEdge (coarse.point i).val)),
          let P := K.folding.projectedBoundaryChain coarse
          ∀ (source closing : Plane), P.RadialFrom source 0 →
            0 < dist source (P.vertex 0) → ∀ (height : Plane →ₗ[ℝ] ℝ),
            (∀ z ∈ Set.range P.path, 0 ≤ height (z - source)) → height (closing - source) < 0 →
            0 < inner ℝ (P.vertex (Fin.last (n + 1)) - source)
              (closing - P.vertex (Fin.last (n + 1))) →
            Schoenflies.IsJordanCurve (P.threeSegmentClosure source closing) →
            ∃ E : K.CompletionMesh φ
                (PlanarTopology.closedJordanDomain (P.threeSegmentClosure source closing))
                (K.combinedCompletionEquations (P.markedClosureEquations source closing)),
              (∀ p ∈ PlanarTopology.closedJordanDomain (P.threeSegmentClosure source closing),
                SpatialEnvelope.height (K.completionPlanes E.tentHeight (Real.sin φ / 2)) p =
                  K.roofHeight p) ∧
              let view := E.originalConstraintView
              let fine := view.originalChainRefinement retain coarse cut
              |C.boundaryChainRollHeading coarse (Fin.last n) -
                E.cap.projectedFanRollHeading view.originalPieceSet fine.chain
                  (Fin.last fine.length)| < η := by
  obtain ⟨φ, bounds, uniform⟩ :=
    exists_uniform_completion_original_bank_heading_error.{u, v} positive
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt retain n coarse cut
  dsimp only
  intro source closing radial initial height supported excluded outward jordan
  let P := K.folding.projectedBoundaryChain coarse
  obtain ⟨E, preserved⟩ := K.exists_combined_completion (P.markedClosureEquations source closing)
    bounds.1 bounds.2 (PlanarTopology.isCompact_closedJordanDomain jordan)
    (P.markedClosureEquations_ne_zero source closing)
  let view := E.originalConstraintView
  let fine := view.originalChainRefinement retain coarse cut
  have refined_radial := fine.cap_projected_radialFrom source radial
  have refined_initial := initial.trans_eq
    (congrArg (dist source) fine.cap_projected_initial).symm
  have refined_supported : ∀ z ∈
      Set.range (view.cap.projectedBoundaryChain view.originalPieceSet fine.chain).path,
      0 ≤ height (z - source) :=
    fun z member => supported z (fine.cap_projected_path_range.subset member)
  have refined_outward : 0 < inner ℝ
      ((view.cap.projectedBoundaryChain view.originalPieceSet fine.chain).vertex
        (Fin.last (fine.length + 1)) - source)
      (closing - (view.cap.projectedBoundaryChain view.originalPieceSet fine.chain).vertex
        (Fin.last (fine.length + 1))) := by
    rw [fine.cap_projected_terminal]
    exact outward
  have refined_jordan : Schoenflies.IsJordanCurve
      ((view.cap.projectedBoundaryChain view.originalPieceSet fine.chain).threeSegmentClosure
        source closing) := Eq.mpr
    (congrArg Schoenflies.IsJordanCurve (fine.cap_projected_closure source closing)) jordan
  have inside := E.extraConstraintView.markedClosure_inside P source closing jordan
  have avoids := E.extraConstraintView.markedClosure_avoids P source closing
  have refined_inside :
      (view.cap.projectedBoundaryChain view.originalPieceSet fine.chain).threeSegmentClosure
        source closing ⊆ interior view.cap.footprint :=
    fun _ member => inside ((fine.cap_projected_closure source closing).subset member)
  have refined_avoids : ∀ f, Disjoint (interior (view.cap.projectedTriangle f).carrier)
      ((view.cap.projectedBoundaryChain view.originalPieceSet fine.chain).threeSegmentClosure
        source closing) := fun f => (avoids f).mono_right
      (fine.cap_projected_closure source closing).subset
  exact ⟨E, preserved, uniform K tilt view retain coarse cut source closing refined_radial
    refined_initial height refined_supported excluded refined_outward refined_jordan
    refined_inside refined_avoids⟩

end Unfoldings.ConvexRoof
