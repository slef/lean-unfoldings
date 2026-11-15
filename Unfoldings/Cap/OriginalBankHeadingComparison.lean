module

public import Unfoldings.Cap.OriginalRadialChainErrorBound
public import Unfoldings.Cap.RadialBankThreshold
public import Unfoldings.Topology.FinitePrefixSum

/-! Uniform comparison for the real unreduced headings of actual original cut banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

local instance originalHeadingMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U : Set Face) {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
  (chain : ((C.restrictFaces U).boundarySystem retain).Chain n)

/-- The same actual one-sided bank fans, measured in the original physical projection. -/
def projectedFanRollHeading : Fin (n + 1) → ℝ :=
  Fin.partialSum (fun i : Fin n => Real.pi - K.projectedCutFanAngle U retain
    ((C.restrictFaces U).boundaryEndVertex retain (chain.point i.succ)))

/-- Every real prefix error is the sum of the actual original one-sided fan errors. -/
theorem boundaryChainRollHeading_sub_projectedFanRollHeading (i : Fin (n + 1)) :
    (C.restrictFaces U).boundaryChainRollHeading chain i - K.projectedFanRollHeading U chain i =
      Fin.partialSum (fun k : Fin n => K.cutBoundaryTurnError U (chain.point k.succ)) i := by
  induction i using Fin.induction with
  | zero => simp only [TriangleComplex.boundaryChainRollHeading,
      projectedFanRollHeading, Fin.partialSum_zero, sub_self]
  | succ k previous =>
    dsimp only [TriangleComplex.boundaryChainRollHeading, projectedFanRollHeading] at previous ⊢
    rw [Fin.partialSum_succ, Fin.partialSum_succ, Fin.partialSum_succ]
    dsimp only [cutBoundaryTurnError] at previous ⊢
    linarith

/-- The terminal error includes every original internal hinge exactly once. -/
theorem boundaryChainRollHeading_sub_projectedFanRollHeading_last :
    (C.restrictFaces U).boundaryChainRollHeading chain (Fin.last n) -
        K.projectedFanRollHeading U chain (Fin.last n) =
      ∑ k : Fin n, K.cutBoundaryTurnError U (chain.point k.succ) := by
  rw [K.boundaryChainRollHeading_sub_projectedFanRollHeading]
  exact fin_partialSum_prefix le_rfl _ _ (fun _ => rfl)

end Unfoldings.ConvexCap

namespace Unfoldings.ConvexCap

universe u v

open Classical in
/-- One positive tilt makes the actual original real-heading error arbitrarily small,
independently of the mesh, path length and valence. Only the initial incident side of
the geometric comparison closure is specified; no fan or rolling certificate is supplied. -/
theorem exists_uniform_tilt_original_bank_heading_error_lt {η : ℝ} (positive : 0 < η) :
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
            0 < K.projectedGermOrientation (C.includeRestrictedGerm U chain.first.val) →
            chain.first.val.1.1.val ∈ K.jordanFaces (P.threeSegmentClosure source closing) →
            |(C.restrictFaces U).boundaryChainRollHeading chain (Fin.last n) -
              K.projectedFanRollHeading U chain (Fin.last n)| < η := by
  obtain ⟨φ, bounds, budget⟩ := exists_uniform_tilt_radial_bank_budget.{u, v} positive
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt U retain n chain
  dsimp only
  intro source closing radial initial height supported excluded outward jordan inside avoids
    positive_first selected
  obtain ⟨corner, total⟩ := budget K tilt
  rw [K.boundaryChainRollHeading_sub_projectedFanRollHeading_last]
  exact (K.abs_sum_original_radial_chain_turnError_le U chain source closing radial initial
    height supported excluded outward jordan inside avoids positive_first selected
    (by positivity) corner bounds.1.le bounds.2 tilt).trans_lt total

end Unfoldings.ConvexCap
