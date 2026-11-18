module

public import Unfoldings.Roof.SupportedOriginalBankWindow
public import Unfoldings.Polyhedron.ProjectedBoundaryChainInterval

/-! Uniformly controlled physical comparisons on short windows of an actual bank chain. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

local instance supportedBankWindowsMeshFintype {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
    {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra) :
    Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

open Classical in
/-- Every short actual bank interval constructs a respected physical cap and its real heading
  bound. -/
def SupportedBankWindowComparisons {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C) (φ η : ℝ)
    (retain : Set C.Seam) {m : ℕ}
    (full : (C.boundarySystem retain).Chain m) (control : Plane) : Prop :=
  ∀ (first n : ℕ) (fits : first + (n + 1) ≤ m),
    let actual := full.interval first (n + 1) fits
    let P := K.folding.projectedBoundaryChain actual
    (∑ k : Fin n, InnerProductGeometry.angle
      (P.internalSourceRay control k.castSucc) (P.internalSourceRay control k.succ)) < Real.pi / 4 →
    ∀ {δ : ℝ}, 0 < δ →
      ∃ cut : ∀ j, ¬ C.IsBoundaryEdge Set.univ
          (C.germEdge (actual.point j).val),
      ∃ (s t : unitInterval) (start : 0 < s.val ∧ s.val < 1) (finish : 0 < t.val ∧ t.val < 1),
        ∃ (q c : Plane) (height : Plane →ₗ[ℝ] ℝ),
        let trimmed := P.trimEnds s t
        dist q control < δ ∧ trimmed.RadialFrom q 0 ∧ 0 < dist q (trimmed.vertex 0) ∧
        (∀ z ∈ Set.range trimmed.path, 0 ≤ height (z - q)) ∧ height (c - q) < 0 ∧
        0 < inner ℝ (trimmed.vertex (Fin.last (n + 2)) - q)
          (c - trimmed.vertex (Fin.last (n + 2))) ∧
        ∃ jordan : Schoenflies.IsJordanCurve (trimmed.threeSegmentClosure q c),
          ∃ E : K.CompletionMesh φ
              (PlanarTopology.closedJordanDomain (trimmed.threeSegmentClosure q c))
              (K.combinedCompletionEquations
                (trimmed.markedClosureEquations q c)),
            (∀ p ∈ PlanarTopology.closedJordanDomain (trimmed.threeSegmentClosure q c),
              SpatialEnvelope.height (K.completionPlanes E.tentHeight
                (Real.sin φ / 2)) p = K.roofHeight p) ∧
            let window := CompletionMesh.markedOriginalBankWindow actual cut s t q c
              start.2 finish.2 jordan E
            |C.boundaryChainRollHeading actual (Fin.last (n + 1)) -
              E.cap.projectedFanRollHeading E.originalConstraintView.originalPieceSet
                window.chain (Fin.last window.length)| < η

end Unfoldings.ConvexRoof
