module

public import Unfoldings.Cap.CenteredTraceValues
public import Unfoldings.Geometry.RecoverableStripClosure

/-! A trace follows both complete banks from the common source through every active height. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {retain : Set C.Seam} (D : FacewiseDevelopment C retain)

theorem centeredMap_exists_bank_trace (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (L : ℝ≥0)
    (linear_bound : ∀ f z, ‖(D.coordinatePlacement K calibration frame f).linear z‖ ≤ L * ‖z‖)
    (S : MonotoneStrip) (E : Set ℂ) (b : ℝ) (finite : E.Finite) (source : (0 : ℂ) ∈ E)
    (first : S.lower.coordinate 0 = 0) (last : S.upper.coordinate 0 = 0)
    (pinches : S.RecoverablePinchesIn E 0 b)
    (inside : ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) → z.re + z.im ∈ Set.Icc 0 b →
      q + frame.symm z ∈ K.footprint ∧ D.ProjectedCoherentAt K (q + frame.symm z)) :
    let domain := {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 b}
    ∃ G : ℂ → ℂ, Continuous G ∧ Set.EqOn (D.centeredMap K q calibration frame) G domain ∧
      ∀ z ∈ domain,
        G 0 = D.centeredMap K q calibration frame 0 ∧
          ∀ h ∈ Set.Icc 0 (z.re + z.im),
            D.TraceVisibleAt K q calibration frame G domain (S.lower.point h) ∧
              D.TraceVisibleAt K q calibration frame G domain (S.upper.point h) := by
  let domain := {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 b}
  obtain ⟨G, continuous, agrees, faces⟩ :=
    D.centeredMap_exists_strip_trace q calibration frame L linear_bound S E 0 b pinches inside
  have visible := D.centered_trace_visible q calibration frame continuous faces
  refine ⟨G, continuous, agrees, ?_⟩
  intro z member
  have positive := S.strict_height_pos_of_source first last member.1 member.2.1
  have banks := S.bank_points_mem_closure_before_active_height finite pinches positive member.2.2
    (member.1.1.trans member.1.2)
  have source_closure := S.source_mem_closure_before_active_height finite first pinches positive
    member.2.2 (member.1.1.trans member.1.2)
  have zero_slab : (0 : ℂ).re + (0 : ℂ).im ∈ Set.Icc 0 b := by
    simp only [Complex.zero_re, Complex.zero_im, zero_add]
    exact ⟨le_rfl, positive.le.trans member.2.2⟩
  have source_coherent := (inside 0 (Or.inr source) zero_slab).2
  refine ⟨D.traceVisibleAt_eq_of_coherent q calibration frame (visible 0 source_closure)
    source_coherent, ?_⟩
  intro h slab
  exact ⟨visible _ (banks h slab).1, visible _ (banks h slab).2⟩

end Unfoldings.FacewiseDevelopment
