module

public import Unfoldings.Cap.OriginalBankHeadingComparison
public import Unfoldings.Cap.SignedOriginalRadialChainErrorBound

/-! Uniform real bank-heading comparison in either physical traversal orientation. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

open Classical in
/-- One positive tilt makes the actual original real-heading error arbitrarily small,
independently of the mesh, path length, valence and traversal orientation.
Only the initial incident side of
the geometric comparison closure is specified; no fan or rolling certificate is supplied. -/
theorem exists_uniform_tilt_original_bank_heading_error_lt_signed {η : ℝ} (positive : 0 < η) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ (U : Set Face) {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
          (chain : ((C.restrictFaces U).boundarySystem retain).Chain n),
          let P := K.projectedBoundaryChain U chain
          ∀ (source closing : Plane), P.RadialFrom source 0 →
            0 < dist source (P.vertex 0) → ∀ (height : Plane →ₗ[ℝ] ℝ),
            (∀ z ∈ Set.range P.path, 0 ≤ height (z - source)) → height (closing - source) < 0 →
            0 < inner ℝ (P.vertex (Fin.last (n + 1)) - source)
              (closing - P.vertex (Fin.last (n + 1))) →
            Schoenflies.IsJordanCurve (P.threeSegmentClosure source closing) →
            P.threeSegmentClosure source closing ⊆ interior K.footprint →
            (∀ f, Disjoint (interior (K.projectedTriangle f).carrier)
              (P.threeSegmentClosure source closing)) →
            chain.first.val.1.1.val ∈ K.jordanFaces (P.threeSegmentClosure source closing) →
            |(C.restrictFaces U).boundaryChainRollHeading chain (Fin.last n) -
              K.projectedFanRollHeading U chain (Fin.last n)| < η := by
  obtain ⟨φ, bounds, budget⟩ := exists_uniform_tilt_radial_bank_budget.{u, v} positive
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt U retain n chain
  dsimp only
  intro source closing radial initial height supported excluded outward jordan inside avoids
    selected
  obtain ⟨corner, total⟩ := budget K tilt
  rw [K.boundaryChainRollHeading_sub_projectedFanRollHeading_last]
  exact (K.abs_sum_original_radial_chain_turnError_le_signed U chain source closing radial initial
    height supported excluded outward jordan inside avoids selected
    (by positivity) corner bounds.1.le bounds.2 tilt).trans_lt total

end Unfoldings.ConvexCap
