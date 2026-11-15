module

public import Unfoldings.Cap.JordanChainErrorBound
public import Unfoldings.Cap.OriginalChainTurnError
public import Unfoldings.Cap.SignedRadialJordanChainLift

/-! Transfer the geometric radial comparison to actual original one-sided cut fans. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

local instance signedOriginalRadialErrorMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U : Set Face) {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
  (chain : ((C.restrictFaces U).boundarySystem retain).Chain n) (source closing : Plane)

local notation "P" => K.projectedBoundaryChain U chain
local notation "J" => PolygonalChain.threeSegmentClosure
  (K.projectedBoundaryChain U chain) source closing

/-- Actual source-radial original cut banks satisfy the geometric curvature-and-tilt
comparison. Original bank identities, selected fans, physical refinement lengths and
heading errors are derived in either orientation. Only the initial incident side
of the closure is specified. -/
theorem abs_sum_original_radial_chain_turnError_le_signed
    (radial : (P).RadialFrom source 0) (initial : 0 < dist source ((P).vertex 0))
    (height : Plane →ₗ[ℝ] ℝ) (supported : ∀ z ∈ Set.range (P).path, 0 ≤ height (z - source))
    (excluded : height (closing - source) < 0)
    (outward : 0 < inner ℝ ((P).vertex (Fin.last (n + 1)) - source)
      (closing - (P).vertex (Fin.last (n + 1))))
    (jordan : Schoenflies.IsJordanCurve J) (inside : J ⊆ interior K.footprint)
    (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)
    (selected : chain.first.val.1.1.val ∈ K.jordanFaces J)
    {ε φ : ℝ} (error_nonnegative : 0 ≤ ε) (error : K.RelativeCornerAngleError ε)
    (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    |∑ k : Fin n, K.cutBoundaryTurnError U (chain.point k.succ)| ≤
      C.totalInteriorAngularDefect Set.univ + 6 * φ + 8 * Real.pi * ε := by
  let V := K.jordanFaces J
  let contains := inside.trans interior_subset
  obtain ⟨d, banks, _headings, _roll⟩ := K.exists_radial_jordan_boundary_chain_signed U chain
    source closing radial initial height supported excluded outward jordan contains avoids
    selected
  have physical := K.projectedBoundaryChain_eq_of_original_banks V U d chain banks
  have curve : (K.projectedBoundaryChain V d).threeSegmentClosure source closing = J := by
    rw [physical]
  have radial_d : (K.projectedBoundaryChain V d).RadialFrom source 0 := by
    rw [physical]
    exact radial
  have initial_d : 0 < dist source ((K.projectedBoundaryChain V d).vertex 0) := by
    rw [physical]
    exact initial
  have supported_d : ∀ z ∈ Set.range (K.projectedBoundaryChain V d).path,
      0 ≤ height (z - source) := by
    rw [physical]
    exact supported
  have outward_d : 0 < inner ℝ ((K.projectedBoundaryChain V d).vertex
      (Fin.last (n + 1)) - source)
        (closing - (K.projectedBoundaryChain V d).vertex (Fin.last (n + 1))) := by
    rw [physical]
    exact outward
  have estimate := K.abs_sum_jordan_chain_turnError_le_radial jordan contains avoids d
    source closing curve inside radial_d initial_d height supported_d excluded outward_d
    error_nonnegative error nonnegative small tilt
  have equality : (∑ k : Fin n, K.restrictedBoundaryTurnError V (d.point k.succ)) =
      ∑ k : Fin n, K.cutBoundaryTurnError U (chain.point k.succ) := by
    apply Finset.sum_congr rfl
    intro k _
    exact (K.cutBoundaryTurnError_univ V (d.point k.succ)).symm.trans
      (K.cutBoundaryTurnError_eq_of_original_banks V U d chain banks k)
  rw [equality] at estimate
  exact estimate

end Unfoldings.ConvexCap
