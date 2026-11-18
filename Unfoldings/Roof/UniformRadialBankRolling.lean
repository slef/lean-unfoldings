module

public import Unfoldings.Roof.SpatialMeshBankWindows
public import Unfoldings.Roof.RadialBankComparisons
public import Unfoldings.Roof.BankRollAccuracy
public import Unfoldings.Geometry.RadialBlockThreshold

/-! One tilt makes actual radial bank rolling uniformly accurate across all physical meshes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

local instance uniformRadialBankRollingIndexFintype {I : Type u} [Fintype I] [Nonempty I]
    {family : I → SpatialPlane} {Z : ℝ} (T : Triangulation family Z) : Fintype T.Index :=
  @Fintype.ofFinite _ T.finite

open Classical in
/-- Thresholds precede every mesh, cut, source and bank. No length or phase certificate is input. -/
theorem exists_uniform_radial_bank_rolling {ε γ : ℝ} (error_positive : 0 < ε)
    (error_small : ε < 1) (gamma_positive : 0 < γ) (gamma_small : γ ≤ 1) :
    ∃ η > 0, ∃ χ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ ψ ∈ Set.Ioc (0 : ℝ) θ,
        (3 : ℝ) / 4 ≤ Real.cos ψ ∧
        radialBlockError (Real.cos ψ)⁻¹ η γ⁻¹
          (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4) < ε ∧
        ∀ {I : Type u} [Fintype I] [Nonempty I] (family : I → SpatialPlane) {Z : ℝ}
          (T : Triangulation family Z) (conforming : TriangleFamily.Conforming T.projectedTriangle)
          (inside : (interior (clip family Z)).Nonempty),
          (∀ i, Real.cos ψ ≤ (family i).normal 2) →
          ∀ (retain : Set T.pairedComplex.Seam) {m : ℕ}
            (full : (T.pairedComplex.boundarySystem retain).Chain m) (control : Plane),
            (T.pairedFolding.projectedBoundaryChain full).RadialFrom control 0 →
            0 < dist control ((T.pairedFolding.projectedBoundaryChain full).vertex 0) →
            (∀ j, Cap.horizontal (T.pairedFolding.boundaryPosition (full.point j)) ∈
              interior (clip family Z)) →
            (∀ j : Fin (m + 1), γ *
              (‖(T.pairedFolding.projectedBoundaryChain full).vertex j.castSucc - control‖ *
                ‖(T.pairedFolding.projectedBoundaryChain full).edge j‖) ≤
              inner ℝ ((T.pairedFolding.projectedBoundaryChain full).vertex j.castSucc - control)
                ((T.pairedFolding.projectedBoundaryChain full).edge j)) →
            let K := T.roof conforming inside
            K.RadialBankComparisons χ η γ retain full control ∧
              K.BankRollAccuracy ε ((Real.cos ψ)⁻¹ * γ⁻¹ / (1 - ε)) retain full := by
  obtain ⟨η, eta_positive, θ₀, theta_bounds, distortion⟩ :=
    exists_positive_radialBlock_threshold error_positive (inv_nonneg.mpr gamma_positive.le)
      (Real.sqrt_nonneg (1 - γ ^ 2))
      (show (0 : ℝ) < Real.pi / 4 from div_pos Real.pi_pos (by norm_num))
  obtain ⟨χ, chi_bounds, uniform⟩ := exists_uniform_spatial_mesh_bank_windows.{u} eta_positive
  let θ := min θ₀ χ
  have theta_positive : 0 < θ := lt_min theta_bounds.1 chi_bounds.1
  have theta_small : θ < Real.pi / 2 := (min_le_left _ _).trans_lt theta_bounds.2
  refine ⟨η, eta_positive, χ, chi_bounds, θ, ⟨theta_positive, theta_small⟩, ?_⟩
  intro ψ psi_bounds
  have psi_theta : ψ ≤ θ₀ := psi_bounds.2.trans (min_le_left _ _)
  have psi_chi : ψ ≤ χ := psi_bounds.2.trans (min_le_right _ _)
  obtain ⟨cos_lower, small_error⟩ := distortion ψ ⟨psi_bounds.1, psi_theta⟩
  refine ⟨cos_lower, small_error, ?_⟩
  intro I _ _ family Z T conforming inside normal retain m full control radial initial domain
    margin
  dsimp only
  let K := T.roof conforming inside
  let P := (T.pairedFolding.projectedBoundaryChain full).inComplexFrame
    (K.projectedBankFrame full)
  let Q := K.framedIntrinsicRoll full
  have normal_chi (i) : Real.cos χ ≤ (family i).normal 2 :=
    (Real.cos_le_cos_of_nonneg_of_le_pi psi_bounds.1.le
      (by linarith [chi_bounds.2, Real.pi_pos]) psi_chi).trans (normal i)
  have strict := (T.pairedFolding.projectedBoundaryChain full).strictRadialSource_of_margin
    gamma_positive radial initial margin
  have windows := uniform family T conforming inside normal_chi retain full control strict
    initial domain
  have data : K.RadialBankComparisons χ η γ retain full control :=
    ⟨chi_bounds, fun f => normal_chi (T.support f), gamma_positive, gamma_small,
      windows, radial, initial, margin⟩
  have cos_positive : 0 < Real.cos ψ := (by norm_num : (0 : ℝ) < 3 / 4).trans_le cos_lower
  have normal_psi (f) : Real.cos ψ ≤ K.normal f 2 := normal (T.support f)
  have chord := ConvexRoof.SupportedBankWindowComparisons.radial_chord_error windows
    eta_positive.le cos_positive normal_psi gamma_positive gamma_small radial initial margin
  have length := ConvexRoof.SupportedBankWindowComparisons.radial_length_bound windows
    eta_positive.le cos_positive normal_psi gamma_positive gamma_small radial initial margin
    (small_error.trans error_small)
  have coefficient : (Real.cos ψ)⁻¹ * γ⁻¹ / (1 - radialBlockError (Real.cos ψ)⁻¹ η γ⁻¹
      (Real.sqrt (1 - γ ^ 2)) (Real.pi / 4)) ≤ (Real.cos ψ)⁻¹ * γ⁻¹ / (1 - ε) :=
    div_le_div_of_nonneg_left (mul_nonneg (inv_nonneg.mpr cos_positive.le)
      (inv_nonneg.mpr gamma_positive.le)) (sub_pos.mpr error_small)
      (sub_le_sub_left small_error.le 1)
  exact ⟨data, ⟨chord.trans (mul_le_mul_of_nonneg_right small_error.le (norm_nonneg _)),
    length.trans (mul_le_mul_of_nonneg_right coefficient (norm_nonneg _))⟩⟩

end Unfoldings.SpatialEnvelope.Triangulation
