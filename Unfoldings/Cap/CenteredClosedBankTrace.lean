module

public import Unfoldings.Cap.CenteredBankTrace
public import Unfoldings.Cap.CenteredTraceInjectivity

/-! Construct actual bank traces injective on the whole approached strip closure. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {retain : Set C.Seam} (D : FacewiseDevelopment C retain)

/-- Retain all visible bank values and full closed-trace injectivity for the same
continuous extension. No equality of distinct cut-vertex copies is assumed. -/
theorem centeredMap_exists_injective_bank_trace (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (L : ℝ≥0)
    (linear_bound : ∀ f z, ‖(D.coordinatePlacement K calibration frame f).linear z‖ ≤ L * ‖z‖)
    (margins : ∀ f j,
      0 < affineAxisMargins (D.coordinatePlacement K calibration frame f).toAffineMap j)
    (S : MonotoneStrip) (E : Set ℂ) (b : ℝ) (finite : E.Finite) (source : (0 : ℂ) ∈ E)
    (first : S.lower.coordinate 0 = 0) (last : S.upper.coordinate 0 = 0)
    (pinches : S.RecoverablePinchesIn E 0 b)
    (inside : ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) → z.re + z.im ∈ Set.Icc 0 b →
      q + frame.symm z ∈ K.footprint ∧ D.ProjectedCoherentAt K (q + frame.symm z)) :
    let domain := {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 b}
    ∃ G : ℂ → ℂ, Continuous G ∧ Set.EqOn (D.centeredMap K q calibration frame) G domain ∧
      Set.InjOn G (closure domain) ∧
      ∀ z ∈ domain,
        G 0 = D.centeredMap K q calibration frame 0 ∧
          ∀ h ∈ Set.Icc 0 (z.re + z.im),
            D.TraceVisibleAt K q calibration frame G domain (S.lower.point h) ∧
              D.TraceVisibleAt K q calibration frame G domain (S.upper.point h) := by
  obtain ⟨G, continuous, equal, traces⟩ := D.centeredMap_exists_bank_trace q calibration frame L
    linear_bound S E b finite source first last pinches inside
  exact ⟨G, continuous, equal,
    D.centeredMap_closed_trace_injective q calibration frame margins S E 0 b pinches inside
      continuous equal, traces⟩

end Unfoldings.FacewiseDevelopment
