module

public import Unfoldings.Roof.SourceStartRoutedBankRolling
public import Unfoldings.Roof.SourceStartMeshBankWindows
public import Unfoldings.Geometry.RadialBlockThreshold

/-! One positive tilt controls complete source-starting routed banks on every physical mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v w

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

local instance uniformSourceStartBankIndexFintype {I : Type w} [Fintype I] [Nonempty I]
    {family : I → SpatialPlane} {Z : ℝ} (T : SpatialEnvelope.Triangulation family Z) :
    Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- One threshold precedes every mesh, cut and complete bank, including its first edge. -/
theorem exists_uniform_sourceStart_routed_bank_rolling
    (positive : 0 < a) (beta : 0 ≤ β) (acute : β < Real.pi / 2)
    {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ G.slopes)
    (upper : ∀ p ∈ G.slopes, ‖p‖ ≤ b)
    (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ ψ ∈ Set.Ioc (0 : ℝ) θ,
      ∀ {I : Type w} [Fintype I] [Nonempty I] (family : I → SpatialPlane) {Z : ℝ}
        (T : SpatialEnvelope.Triangulation family Z)
        (_conforming : TriangleFamily.Conforming T.projectedTriangle)
        (_inside : (interior (SpatialEnvelope.clip family Z)).Nonempty),
        (∀ i, Real.cos ψ ≤ (family i).normal 2) →
        ∀ (retain : Set T.pairedComplex.Seam) {m : ℕ}
          (full : (T.pairedComplex.boundarySystem retain).Chain m),
          R.Follows (T.pairedFolding.projectedBoundaryChain full) →
          (∀ j, Cap.horizontal (T.pairedFolding.boundaryPosition (full.point j)) ∈
            interior (SpatialEnvelope.clip family Z)) →
          (T.pairedComplex.boundaryChainRoll full).GloballyRadiallyMonotone := by
  let γ := Real.cos (2 * annularHistoryAngle (a / b) β)
  have gamma_positive : 0 < γ := fine_annular_radial_margin_pos small
  obtain ⟨η, eta_positive, θ₀, theta_bounds, distortion⟩ :=
    exists_positive_radialBlock_threshold gamma_positive (inv_nonneg.mpr gamma_positive.le)
      (Real.sqrt_nonneg (1 - γ ^ 2))
      (show 0 < Real.pi / 4 from div_pos Real.pi_pos (by norm_num))
  obtain ⟨φ, phi_bounds, windows⟩ :=
    SpatialEnvelope.Triangulation.exists_uniform_spatial_mesh_sourceStart_bank_windows.{w}
      eta_positive
  let θ := min θ₀ φ
  refine ⟨θ, ⟨lt_min theta_bounds.1 phi_bounds.1,
    (min_le_left _ _).trans_lt theta_bounds.2⟩, ?_⟩
  intro ψ psi_bounds I _ _ family Z T conforming inside normal retain m full follows domain
  have psi_theta : ψ ≤ θ₀ := psi_bounds.2.trans (min_le_left _ _)
  have psi_phi : ψ ≤ φ := psi_bounds.2.trans (min_le_right _ _)
  obtain ⟨cos_lower, small_error⟩ := distortion ψ ⟨psi_bounds.1, psi_theta⟩
  have cos_positive : 0 < Real.cos ψ := (by norm_num : (0 : ℝ) < 3 / 4).trans_le cos_lower
  have normal_phi (i) : Real.cos φ ≤ (family i).normal 2 :=
    (Real.cos_le_cos_of_nonneg_of_le_pi psi_bounds.1.le
      (by linarith [phi_bounds.2, Real.pi_pos]) psi_phi).trans (normal i)
  let P := T.pairedFolding.projectedBoundaryChain full
  have physical_outward := R.follows_outward P follows positive beta acute bpos ratio
    inner_disk upper small
  have radial : P.RadialFrom (P.vertex 0) 0 := by
    intro i earlier
    exact (P.radiallyMonotone_iff_outward.mpr physical_outward) 0 i earlier
  have margin (i : Fin (m + 1)) : γ * (‖P.vertex i.castSucc - P.vertex 0‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - P.vertex 0) (P.edge i) :=
    R.follows_subhistory_radial_margin P follows positive beta acute bpos ratio inner_disk upper
      small 0 i (Nat.zero_le _)
  have comparisons := windows family T conforming inside normal_phi retain full radial
    gamma_positive margin domain
  exact R.sourceStart_intrinsicBank_globallyRadiallyMonotone comparisons follows positive beta
    acute bpos ratio inner_disk upper small eta_positive.le cos_positive
    (fun f => normal (T.support f)) small_error

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
