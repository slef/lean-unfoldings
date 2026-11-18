module

public import Unfoldings.Roof.SupportedRadialBankRolling

/-! One actual bank chain carries both constructed cap comparisons and its physical radial data. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Physical data on one chain; the rolling estimates are derived, rather than supplied. -/
structure RadialBankComparisons (φ η γ : ℝ) (retain : Set C.Seam) {m : ℕ}
    (full : (C.boundarySystem retain).Chain m) (control : Plane) : Prop where
  angle : φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  tilt : K.TiltBound φ
  gamma_positive : 0 < γ
  gamma_small : γ ≤ 1
  windows : K.SupportedBankWindowComparisons φ η retain full control
  radial : (K.folding.projectedBoundaryChain full).RadialFrom control 0
  initial : 0 < dist control ((K.folding.projectedBoundaryChain full).vertex 0)
  margin : ∀ i : Fin (m + 1), γ *
    (‖(K.folding.projectedBoundaryChain full).vertex i.castSucc - control‖ *
      ‖(K.folding.projectedBoundaryChain full).edge i‖) ≤
    inner ℝ ((K.folding.projectedBoundaryChain full).vertex i.castSucc - control)
      ((K.folding.projectedBoundaryChain full).edge i)

namespace RadialBankComparisons

variable {K} {φ η γ : ℝ} {retain : Set C.Seam} {m : ℕ}
  {full : (C.boundarySystem retain).Chain m} {control : Plane}
  (data : K.RadialBankComparisons φ η γ retain full control)

include data in
theorem cos_positive : 0 < Real.cos φ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [data.angle.1, Real.pi_pos], data.angle.2⟩

include data in
/-- The original intrinsic roll's length bound depends only on tilt, radial margin and error. -/
theorem length_bound (nonnegative : 0 ≤ η)
    (small : radialBlockError (Real.cos φ)⁻¹ η γ⁻¹
      (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4) < 1) :
    (C.boundaryChainRoll full).projectedLength ≤
      ((Real.cos φ)⁻¹ * γ⁻¹ / (1 - radialBlockError (Real.cos φ)⁻¹ η γ⁻¹
        (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4))) *
      ‖(C.boundaryChainRoll full).vertex (Fin.last (m + 1)) -
        (C.boundaryChainRoll full).vertex 0‖ :=
  SupportedBankWindowComparisons.radial_length_bound data.windows nonnegative
    data.cos_positive data.tilt
    data.gamma_positive data.gamma_small data.radial data.initial data.margin small

include data in
/-- The actual physical reference determines the full original roll's aligned chord error. -/
theorem chord_error (nonnegative : 0 ≤ η) :
    let P := (K.folding.projectedBoundaryChain full).inComplexFrame (K.projectedBankFrame full)
    let Q := K.framedIntrinsicRoll full
    ‖polarRay (-K.projectedMetricHeadingError full (Fin.last m)) *
        (Q.vertex (Fin.last (m + 1)) - Q.vertex 0) -
      (P.vertex (Fin.last (m + 1)) - P.vertex 0)‖ ≤
      radialBlockError (Real.cos φ)⁻¹ η γ⁻¹ (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4) *
        ‖P.vertex (Fin.last (m + 1)) - P.vertex 0‖ :=
  SupportedBankWindowComparisons.radial_chord_error data.windows nonnegative data.cos_positive
    data.tilt
    data.gamma_positive data.gamma_small data.radial data.initial data.margin

end RadialBankComparisons
end Unfoldings.ConvexRoof
