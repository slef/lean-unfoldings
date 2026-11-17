module

public import Unfoldings.Roof.CompletionChainHeading
public import Unfoldings.Cap.UnconditionalOriginalBankHeadingComparison

/-! Uniform physical comparison bounds apply to the original cut bank's real heading. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

local instance completionOriginalComparisonIndexFintype {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
    (E : K.CompletionMesh φ region K.originalEdgeEquations) :
    Fintype E.partition.Index := @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- One tilt compares every original cut bank's unreduced real terminal heading
with its actual physical projected fans. The completion constructs all fine banks;
neither orientation, a selected Jordan side, nor a fan-angle match is a premise.
Only the radial closure geometry of the constructed fine chain is required. -/
theorem exists_uniform_completion_original_bank_heading_error {η : ℝ} (positive : 0 < η) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
        K.TiltBound φ → ∀ {region : Set Plane}
          (E : K.CompletionMesh φ region K.originalEdgeEquations)
          (retain : Set C.Seam) {n : ℕ} (coarse : (C.boundarySystem retain).Chain n)
          (cut : ∀ i, ¬ C.IsBoundaryEdge Set.univ (C.germEdge (coarse.point i).val)),
          let fine := E.originalChainRefinement retain coarse cut
          let P := E.cap.projectedBoundaryChain E.originalPieceSet fine.chain
          ∀ (source closing : Plane), P.RadialFrom source 0 →
            0 < dist source (P.vertex 0) → ∀ (height : Plane →ₗ[ℝ] ℝ),
            (∀ z ∈ Set.range P.path, 0 ≤ height (z - source)) → height (closing - source) < 0 →
            0 < inner ℝ (P.vertex (Fin.last (fine.length + 1)) - source)
              (closing - P.vertex (Fin.last (fine.length + 1))) →
            Schoenflies.IsJordanCurve (P.threeSegmentClosure source closing) →
            P.threeSegmentClosure source closing ⊆ interior E.cap.footprint →
            (∀ f, Disjoint (interior (E.cap.projectedTriangle f).carrier)
              (P.threeSegmentClosure source closing)) →
            |C.boundaryChainRollHeading coarse (Fin.last n) -
              E.cap.projectedFanRollHeading E.originalPieceSet fine.chain (Fin.last fine.length)| <
                η := by
  obtain ⟨φ, bounds, uniform⟩ :=
    ConvexCap.exists_uniform_tilt_original_bank_heading_error_lt_unconditional.{0, 0} positive
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt region E retain n coarse cut
  dsimp only
  intro source closing radial initial height supported excluded outward jordan inside avoids
  let fine := E.originalChainRefinement retain coarse cut
  have estimate := uniform E.cap (CompletionMesh.cap_tilt bounds.1 bounds.2 tilt)
    E.originalPieceSet fine.chain source closing radial initial height supported excluded outward
    jordan inside avoids
  exact (congrArg (fun heading : ℝ => |heading - E.cap.projectedFanRollHeading
    E.originalPieceSet fine.chain (Fin.last fine.length)|) fine.terminal_heading_eq.symm).trans_lt
    estimate

end Unfoldings.ConvexRoof
