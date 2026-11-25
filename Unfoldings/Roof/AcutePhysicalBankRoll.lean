module

public import Unfoldings.Roof.AcuteBankWindows
public import Unfoldings.Roof.BankRollAccuracy
public import Unfoldings.Geometry.HeadingSpeedError
public import Unfoldings.Geometry.ChordRotationControl
public import Unfoldings.Geometry.ComplexFrameSubhistories
public import Unfoldings.Geometry.NextEdgeRadialBlocks

/-! Uniform sharp chord comparisons on the physical bank in an acute heading cone. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The acute-cone error controls the intrinsic roll and its terminal outward
direction. The chord is aligned to the actual outgoing tangent. -/
theorem sharp_acute_physical_bank_roll
    {φ γ A : ℝ} (positive : 0 < φ) (small_phi : φ < π / 2)
    (height_bound : (3 : ℝ) / 4 ≤ cos φ) (tilt : K.TiltBound φ)
    (gamma_positive : 0 < γ) (gamma_le : γ ≤ 1) (length_nonneg : 0 ≤ A)
    {retain : Set C.Seam} {n : ℕ} (bank : (C.boundarySystem retain).Chain n)
    (cut : ∀ i, ¬ C.IsBoundaryEdge Set.univ (C.germEdge (bank.point i).val))
    (h k : Plane →L[ℝ] ℝ) (joint : Function.Bijective fun p => (h p, k p))
    (controls : let P := K.folding.projectedBoundaryChain bank
      (∀ i, 0 < h (P.edge i)) ∧ (∀ i, 0 < k (P.edge i)))
    (margin : let P := K.folding.projectedBoundaryChain bank
      ∀ i, γ * (‖P.vertex i.castSucc - P.vertex 0‖ * ‖P.edge i‖) ≤
        inner ℝ (P.vertex i.castSucc - P.vertex 0) (P.edge i))
    (lengths : let P := K.folding.projectedBoundaryChain bank
      ∀ j : Fin (n + 2), (P.interval 0 j.val (PolygonalChain.initial_interval_fits j)).projectedLength ≤
        A * ‖P.vertex j - P.vertex 0‖)
    (small : acuteConeDevelopmentError φ A < γ) :
    let E := acuteConeDevelopmentError φ A
    let D := (cos φ)⁻¹ * A / (1 - E)
    let d := (γ - E) / (1 + E)
    let roll := C.boundaryChainRoll bank
    K.BankRollAccuracy E D retain bank ∧
      d * (‖roll.vertex (Fin.last n).castSucc - roll.vertex 0‖ * ‖roll.edge (Fin.last n)‖) ≤
        inner ℝ (roll.vertex (Fin.last n).castSucc - roll.vertex 0) (roll.edge (Fin.last n)) := by
  let P₀ := K.folding.projectedBoundaryChain bank
  let L := K.projectedBankFrame bank
  let P := P₀.inComplexFrame L
  let Q := K.framedIntrinsicRoll bank
  let error := K.projectedMetricHeadingError bank
  let factor (i : Fin (n + 1)) := K.projectedMetricStretch (bank.point i)
  let changed := K.framedIntrinsicRoll_edge_factor bank
  let E := acuteConeDevelopmentError φ A
  let S := (cos φ)⁻¹
  let B := acuteConeDevelopmentHeading φ
  let D := S * A / (1 - E)
  let d := (γ - E) / (1 + E)
  let i₀ := Fin.last n
  have cos_pos : 0 < cos φ := (by norm_num : (0 : ℝ) < 3 / 4).trans_le height_bound
  have stretch (i) : 1 ≤ factor i ∧ factor i ≤ S :=
    K.projectedMetricStretch_bounds cos_pos tilt (bank.point i)
  have speed : 1 ≤ S := (stretch 0).1.trans (stretch 0).2
  have budget : 0 ≤ B :=
    acuteConeDevelopmentHeading_nonneg positive.le (by linarith only [small_phi, pi_pos])
  have E_nonneg : 0 ≤ E := by
    change 0 ≤ A * (S - 1) + A * S * B
    positivity
  have radial : P₀.RadialFrom (P₀.vertex 0) 0 := by
    intro i _
    apply (monotone_dist_lineMap_iff _ _ _).mpr
    exact (mul_nonneg gamma_positive.le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans
      (margin i)
  have headings (i : Fin (n + 1)) : |error i - error i₀| ≤ B :=
    K.abs_projectedMetricHeadingError_sub_le_sharp_of_acute_controls positive small_phi
      height_bound tilt bank cut (P₀.vertex 0) radial h k joint controls.1 controls.2
      i (Fin.last n) (Fin.le_last i)
  have fitted_lengths (j : Fin (n + 2)) :
      (P.interval 0 j.val (PolygonalChain.initial_interval_fits j)).projectedLength ≤
        A * ‖P.vertex j - P.vertex 0‖ := by
    rw [P₀.inComplexFrame_interval_projectedLength, P₀.inComplexFrame_norm_sub]
    exact lengths j
  have initial_chord (j : Fin (n + 2)) :
      ‖polarRay (-error i₀) * (Q.vertex j - Q.vertex 0) - (P.vertex j - P.vertex 0)‖ ≤
        E * ‖P.vertex j - P.vertex 0‖ := by
    let X := P.interval 0 j.val (PolygonalChain.initial_interval_fits j)
    let Y := Q.interval 0 j.val (PolygonalChain.initial_interval_fits j)
    let index (i : Fin j.val) : Fin (n + 1) := ⟨i.val, by omega⟩
    have factors (i : Fin j.val) :
        Y.edge i = (factor (index i) : ℂ) * polarRay (error (index i)) * X.edge i := by
      simpa only [Y, X, PolygonalChain.interval_edge, Nat.zero_add, index] using changed (index i)
    have chord := X.heading_speed_chord_error Y (error ∘ index) (factor ∘ index) factors
      (anchor := error i₀) (fun i => (stretch (index i)).1) (fun i => (stretch (index i)).2)
    have variation : (∑ i : Fin j.val, |error (index i) - error i₀| * ‖X.edge i‖) ≤
        B * X.projectedLength := by
      rw [PolygonalChain.projectedLength, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (headings (index i)) (norm_nonneg _)
    have loss : (S - 1) * X.projectedLength + S * (B * X.projectedLength) ≤
        E * ‖P.vertex j - P.vertex 0‖ := by
      calc
        _ = ((S - 1) + S * B) * X.projectedLength := by ring
        _ ≤ ((S - 1) + S * B) * (A * ‖P.vertex j - P.vertex 0‖) :=
          mul_le_mul_of_nonneg_left (fitted_lengths j) (by positivity)
        _ = _ := by
          change _ = (A * (S - 1) + A * S * B) * ‖P.vertex j - P.vertex 0‖
          ring
    have weighted :
        (S - 1) * X.projectedLength + S * (∑ i, |error (index i) - error i₀| * ‖X.edge i‖) ≤
          (S - 1) * X.projectedLength + S * (B * X.projectedLength) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left variation (zero_le_one.trans speed))
    simpa only [X, Y, PolygonalChain.interval_start, PolygonalChain.interval_last,
      Nat.zero_add, Fin.eta, show (⟨0, by omega⟩ : Fin (n + 2)) = 0 from Fin.ext rfl] using chord.trans (weighted.trans loss)
  have full : P.projectedLength ≤ A * ‖P.vertex (Fin.last (n + 1)) - P.vertex 0‖ := by
    have identity : P.interval 0 (n + 1) (by simp) = P := by
      cases P
      simp only [PolygonalChain.interval, Nat.zero_add, Fin.eta]
    have bound := fitted_lengths (Fin.last (n + 1))
    change (P.interval 0 (n + 1) (by simp)).projectedLength ≤ _ at bound
    rwa [identity] at bound
  have length : Q.projectedLength ≤ (S * A) * ‖P.vertex (Fin.last (n + 1)) - P.vertex 0‖ := by
    calc
      _ ≤ S * P.projectedLength := P.heading_speed_length_bound Q error factor changed
        (fun i => zero_le_one.trans (stretch i).1) (fun i => (stretch i).2)
      _ ≤ S * (A * ‖P.vertex (Fin.last (n + 1)) - P.vertex 0‖) :=
        mul_le_mul_of_nonneg_left full (zero_le_one.trans speed)
      _ = _ := by ring
  have grown := length_constant_of_aligned_chord_error (error i₀)
    (mul_nonneg (zero_le_one.trans speed) length_nonneg) (small.trans_le gamma_le)
    (initial_chord (Fin.last (n + 1))) length
  have fitted_margin : γ * (‖P.vertex i₀.castSucc - P.vertex 0‖ * ‖P.edge i₀‖) ≤
      inner ℝ (P.vertex i₀.castSucc - P.vertex 0) (P.edge i₀) := by
    rw [P₀.inComplexFrame_chord_inner, P₀.inComplexFrame_norm_sub, P₀.inComplexFrame_edge, L.norm_map]
    exact margin i₀
  have next := radial_margin_of_aligned_chord_error (error i₀) E_nonneg small
    (initial_chord i₀.castSucc) fitted_margin
  have scale : Q.edge i₀ = factor i₀ • (polarRay (error i₀) * P.edge i₀) := by
    rw [changed]
    change (factor i₀ : ℂ) * polarRay (error i₀) * P.edge i₀ =
      (factor i₀ : ℂ) * (polarRay (error i₀) * P.edge i₀)
    ring
  have next' : d * (‖Q.vertex i₀.castSucc - Q.vertex 0‖ * ‖Q.edge i₀‖) ≤
      inner ℝ (Q.vertex i₀.castSucc - Q.vertex 0) (Q.edge i₀) := by
    rw [scale, norm_smul, Real.norm_of_nonneg (zero_le_one.trans (stretch i₀).1),
      real_inner_smul_right]
    have left : d * (‖Q.vertex i₀.castSucc - Q.vertex 0‖ *
        (factor i₀ * ‖polarRay (error i₀) * P.edge i₀‖)) =
        factor i₀ * (d * (‖Q.vertex i₀.castSucc - Q.vertex 0‖ *
          ‖polarRay (error i₀) * P.edge i₀‖)) := by ring
    rw [left]
    exact mul_le_mul_of_nonneg_left next (zero_le_one.trans (stretch i₀).1)
  let rotation := complexRotation (K.projectedBankPhase bank)
  let roll := C.boundaryChainRoll bank
  have chord_next : Q.vertex i₀.castSucc - Q.vertex 0 =
      rotation (roll.vertex i₀.castSucc - roll.vertex 0) := by
    change polarRay (K.projectedBankPhase bank) * roll.vertex i₀.castSucc -
      polarRay (K.projectedBankPhase bank) * roll.vertex 0 = _
    rw [← mul_sub]
    rfl
  have edge_next : Q.edge i₀ = rotation (roll.edge i₀) := K.framedIntrinsicRoll_edge bank _
  change K.BankRollAccuracy E D retain bank ∧ _
  refine ⟨⟨initial_chord (Fin.last (n + 1)), ?_⟩, ?_⟩
  · simpa only [Q, K.framedIntrinsicRoll_projectedLength, K.framedIntrinsicRoll_chord_norm]
      using grown
  · simpa only [chord_next, edge_next, rotation.norm_map, rotation.inner_map_map] using next'

end Unfoldings.ConvexRoof
