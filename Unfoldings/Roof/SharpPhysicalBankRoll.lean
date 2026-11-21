module

public import Unfoldings.Roof.SharpBankWindows
public import Unfoldings.Roof.BankRollAccuracy
public import Unfoldings.Geometry.SharpRadialD4
public import Unfoldings.Geometry.ComplexFrameSubhistories

/-! The exact radial-block development constants for actual roof boundary banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The sharp heading allowance is a nonnegative sum at an acute positive tilt. -/
theorem shallowDevelopmentHeading_nonneg_of_cos {φ : ℝ}
    (positive : 0 ≤ φ) (small : φ ≤ π) (cos_pos : 0 < cos φ) :
    0 ≤ shallowDevelopmentHeading φ := by
  have sec := sub_nonneg.mpr (one_le_inv₀ cos_pos |>.mpr (cos_le_one φ))
  have curvature : 0 ≤ shallowDevelopmentCurvature φ :=
    mul_nonneg (by positivity) (sub_nonneg.mpr (cos_le_one φ))
  unfold shallowDevelopmentHeading
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (arcsin_nonneg.mpr (sq_nonneg _))))
    (mul_nonneg (by positivity) sec))
    (mul_nonneg (mul_nonneg (by norm_num) positive) (sin_nonneg_of_nonneg_of_le_pi positive small)))
    (mul_nonneg (by norm_num) curvature)

open Classical in
/-- The actual intrinsic roll satisfies both D.4 bounds. The projected reference
needs the radial margin and the length bound from its starting point to each
vertex. The next-edge estimate includes an uncharged last outgoing link. -/
theorem sharp_physical_bank_roll
    {φ γ A : ℝ} (positive : 0 < φ) (small_phi : φ < π / 2)
    (height_bound : (3 : ℝ) / 4 ≤ cos φ) (tilt : K.TiltBound φ)
    (gamma_positive : 0 < γ) (gamma_le : γ ≤ 1) (length_nonneg : 0 ≤ A)
    {retain : Set C.Seam} {n : ℕ} (bank : (C.boundarySystem retain).Chain n)
    (cut : ∀ i, ¬ C.IsBoundaryEdge Set.univ (C.germEdge (bank.point i).val))
    (margin : let P := K.folding.projectedBoundaryChain bank
      ∀ i, γ * (‖P.vertex i.castSucc - P.vertex 0‖ * ‖P.edge i‖) ≤
        inner ℝ (P.vertex i.castSucc - P.vertex 0) (P.edge i))
    (lengths : let P := K.folding.projectedBoundaryChain bank
      ∀ j : Fin (n + 2), (P.interval 0 j.val (PolygonalChain.initial_interval_fits j)).projectedLength ≤
        A * ‖P.vertex j - P.vertex 0‖)
    (small : radialBlockError (cos φ)⁻¹ (shallowDevelopmentHeading φ) A
      (sqrt (1 - γ ^ 2)) π < γ) :
    let E := radialBlockError (cos φ)⁻¹ (shallowDevelopmentHeading φ) A (sqrt (1 - γ ^ 2)) π
    let D := (cos φ)⁻¹ * A / (1 - E)
    let d := (γ - E) / (1 + E)
    let Q := C.boundaryChainRoll bank
    K.BankRollAccuracy E D retain bank ∧
      d * (‖Q.vertex (Fin.last n).castSucc - Q.vertex 0‖ * ‖Q.edge (Fin.last n)‖) ≤
        inner ℝ (Q.vertex (Fin.last n).castSucc - Q.vertex 0) (Q.edge (Fin.last n)) := by
  let P₀ := K.folding.projectedBoundaryChain bank
  let L := K.projectedBankFrame bank
  let P := P₀.inComplexFrame L
  let Q := K.framedIntrinsicRoll bank
  let source := P₀.vertex 0
  let E := radialBlockError (cos φ)⁻¹ (shallowDevelopmentHeading φ) A (sqrt (1 - γ ^ 2)) π
  let D := (cos φ)⁻¹ * A / (1 - E)
  let d := (γ - E) / (1 + E)
  have cos_pos : 0 < cos φ := (by norm_num : (0 : ℝ) < 3 / 4).trans_le height_bound
  have stretch (i) := K.projectedMetricStretch_bounds cos_pos tilt (bank.point i)
  have speed : 1 ≤ (cos φ)⁻¹ := (stretch 0).1.trans (stretch 0).2
  have budget := shallowDevelopmentHeading_nonneg_of_cos positive.le
    (by linarith only [small_phi, pi_pos]) cos_pos
  have radial : P₀.RadialFrom source 0 := by
    intro i _
    apply (monotone_dist_lineMap_iff _ _ _).mpr
    exact (mul_nonneg gamma_positive.le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans
      (margin i)
  have fitted_margin (i) : γ * (‖P.vertex i.castSucc - L source‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - L source) (P.edge i) := by
    rw [P₀.inComplexFrame_radial_inner, P₀.inComplexFrame_radius, P₀.inComplexFrame_edge, L.norm_map]
    exact margin i
  have fitted_lengths (j : Fin (n + 2)) :
      (P.interval 0 j.val (PolygonalChain.initial_interval_fits j)).projectedLength ≤
        A * ‖P.vertex j - P.vertex 0‖ := by
    rw [P₀.inComplexFrame_interval_projectedLength, P₀.inComplexFrame_norm_sub]
    exact lengths j
  have full_length : P.projectedLength ≤ A * ‖P.vertex (Fin.last (n + 1)) - P.vertex 0‖ := by
    have identity : P.interval 0 (n + 1) (by simp) = P := by
      cases P
      simp only [PolygonalChain.interval, Nat.zero_add, Fin.eta]
    have bound := fitted_lengths (Fin.last (n + 1))
    change (P.interval 0 (n + 1) (by simp)).projectedLength ≤ _ at bound
    rwa [identity] at bound
  have prefix_bound (i : Fin (n + 1)) :
      (P.interval 0 i.val (PolygonalChain.initial_interval_fits i.castSucc)).projectedLength ≤
        A * ‖P.vertex i.castSucc - L source‖ :=
    fitted_lengths i.castSucc
  let error := K.projectedMetricHeadingError bank
  let factor (i) := K.projectedMetricStretch (bank.point i)
  have window := K.abs_projectedMetricHeadingError_sub_le_sharp_of_halfturn
    positive small_phi height_bound tilt bank cut source radial gamma_positive margin L
  have chord := P.local_window_chord_error_at_pi Q (L source) error factor
    (K.framedIntrinsicRoll_edge_factor bank) speed budget length_nonneg
    (fun i => (stretch i).1) (fun i => (stretch i).2) gamma_positive.le gamma_le
    fitted_margin prefix_bound window full_length
  have both := P.sharp_developed_chord_margins Q (L source) error factor
    (K.framedIntrinsicRoll_edge_factor bank) speed budget length_nonneg
    (fun i => (stretch i).1) (fun i => (stretch i).2) gamma_positive.le gamma_le
    fitted_margin prefix_bound window full_length small 0 (by simp)
  have next := P.sharp_next_edge_radial_margin Q (L source) error factor
    (K.framedIntrinsicRoll_edge_factor bank) speed budget length_nonneg
    (fun i => (stretch i).1) (fun i => (stretch i).2) gamma_positive.le gamma_le
    fitted_margin prefix_bound window (fitted_lengths (Fin.last n).castSucc) small
    (fitted_margin (Fin.last n))
  let rotation := complexRotation (K.projectedBankPhase bank)
  let roll := C.boundaryChainRoll bank
  have chord_next : Q.vertex (Fin.last n).castSucc - Q.vertex 0 =
      rotation (roll.vertex (Fin.last n).castSucc - roll.vertex 0) := by
    change polarRay (K.projectedBankPhase bank) * roll.vertex (Fin.last n).castSucc -
      polarRay (K.projectedBankPhase bank) * roll.vertex 0 = _
    rw [← mul_sub]
    rfl
  have edge_next : Q.edge (Fin.last n) = rotation (roll.edge (Fin.last n)) :=
    K.framedIntrinsicRoll_edge bank _
  change K.BankRollAccuracy E D retain bank ∧ _
  refine ⟨⟨chord, ?_⟩, ?_⟩
  · simpa only [Q, K.framedIntrinsicRoll_projectedLength,
      K.framedIntrinsicRoll_chord_norm] using both.2
  · simpa only [chord_next, edge_next, rotation.norm_map, rotation.inner_map_map] using next

end Unfoldings.ConvexRoof
