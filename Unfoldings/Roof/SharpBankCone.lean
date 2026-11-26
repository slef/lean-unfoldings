module

public import Unfoldings.Roof.ProjectedBankFrames
public import Unfoldings.Geometry.ComplexFrameLength
public import Unfoldings.Geometry.AcuteBankCone
public import Unfoldings.Geometry.ConjugateGapAngle
public import Unfoldings.Geometry.SourceOpeningBankGap
public import Unfoldings.Geometry.TerminalEdgeRay
public import Mathlib.Analysis.Complex.Isometry

/-! A uniform bound on heading differences adds just its width to an actual bank's cone. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real

/-- Isometric changes of a complex frame preserve an interval of unwrapped
polar headings up to a common rotation and possible reversal. -/
theorem exists_polarHeadings_of_isometry {ι : Type*} (E : ℂ ≃ₗᵢ[ℝ] ℂ)
    (p : ι → ℂ) {lo hi : ℝ} (headings : ∀ i, (p i).arg ∈ Set.Icc lo hi) :
    ∃ (start : ℝ) (heading : ι → ℝ),
      (∀ i, heading i ∈ Set.Icc start (start + (hi - lo))) ∧
      ∀ i, E (p i) = (‖p i‖ : ℂ) * polarRay (heading i) := by
  obtain ⟨c, kind⟩ := linear_isometry_complex E
  have unit : (c : ℂ) = polarRay (c : ℂ).arg := by
    have h : (‖(c : ℂ)‖ : ℂ) * polarRay (c : ℂ).arg = c :=
      Complex.norm_mul_exp_arg_mul_I c
    simpa only [Circle.norm_coe, Complex.ofReal_one, one_mul] using h.symm
  rcases kind with equal | equal
  · let θ := (c : ℂ).arg
    refine ⟨θ + lo, fun i => θ + (p i).arg, fun i => ?_, fun i => ?_⟩
    · have h := headings i
      exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
    rw [equal, rotation_apply, unit, polarRay_add]
    have polar : (‖p i‖ : ℂ) * polarRay (p i).arg = p i := Complex.norm_mul_exp_arg_mul_I _
    exact (congrArg (fun z : ℂ => polarRay θ * z) polar.symm).trans (by ring)
  · let θ := (c : ℂ).arg
    refine ⟨θ - hi, fun i => θ + -(p i).arg, fun i => ?_, fun i => ?_⟩
    · have h := headings i
      exact ⟨by linarith only [h.2], by linarith only [h.1]⟩
    rw [equal, LinearIsometryEquiv.trans_apply, rotation_apply, unit, polarRay_add]
    have polar : Complex.conjLIE (p i) = (‖p i‖ : ℂ) * polarRay (-(p i).arg) := by
      change starRingEnd ℂ (p i) = _
      have original : (‖p i‖ : ℂ) * polarRay (p i).arg = p i := Complex.norm_mul_exp_arg_mul_I _
      exact (congrArg (starRingEnd ℂ) original.symm).trans (by
        simp only [map_mul, Complex.conj_ofReal, conj_polarRay])
    exact (congrArg (fun z : ℂ => polarRay θ * z) polar).trans (by ring)


namespace ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

set_option maxHeartbeats 1100000 in
/-- A bound on the oscillation of the unreduced heading error contributes just
that bound to the width of the cone containing the bank and its opening. -/
theorem exists_common_acuteCone_of_headingOscillation {retain : Set C.Seam} {n : ℕ}
    (bank : (C.boundarySystem retain).Chain n) (E : Plane ≃ₗᵢ[ℝ] ℂ)
    {lo hi error opening : ℝ}
    (headings : ∀ i, (E ((K.folding.projectedBoundaryChain bank).edge i)).arg ∈ Set.Icc lo hi)
    (oscillation : ∀ i j : Fin (n + 1),
      |K.projectedMetricHeadingError bank i - K.projectedMetricHeadingError bank j| ≤ error)
    (opening_nonneg : 0 ≤ opening) (acute : hi - lo + error + opening < π / 2) :
    let R := (C.boundaryChainRoll bank).terminalEdgeRay
    ∃ center : ℝ, R.InAcuteCone center ∧ (R.rotateSuffix 0 opening).InAcuteCone center := by
  let P := K.folding.projectedBoundaryChain bank
  let S := K.projectedBankFrame bank
  let R := (C.boundaryChainRoll bank).terminalEdgeRay
  let phase := K.projectedBankPhase bank
  let e := K.projectedMetricHeadingError bank
  obtain ⟨start, heading, span, polar⟩ :=
    exists_polarHeadings_of_isometry (E.symm.trans S) (fun i => E (P.edge i)) headings
  obtain ⟨j, _, least⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
  let low := start + e j - phase
  let width := hi - lo + error + opening
  let center := low + width / 2
  let h (i : Fin (n + 1)) := heading i + e i - phase
  have between (i : Fin (n + 1)) : h i ∈ Set.Icc low (low + width - opening) := by
    have bottom := least i (Finset.mem_univ i)
    have upper := (abs_le.mp (oscillation i j)).2
    exact ⟨by linarith only [(span i).1, bottom], by linarith only [(span i).2, upper]⟩
  let scale (i : Fin (n + 1)) := K.projectedMetricStretch (bank.point i) * ‖P.edge i‖
  have scale_nonneg (i : Fin (n + 1)) : 0 ≤ scale i :=
    mul_nonneg (div_nonneg (C.boundaryBankLength_pos _).le
      (K.projectedMetricComplex.boundaryBankLength_pos _).le) (norm_nonneg _)
  have polarized (i : Fin (n + 1)) :
      R.chain.edge i = (scale i : ℂ) * polarRay (h i) := by
    have coord : S (P.edge i) = (‖P.edge i‖ : ℂ) * polarRay (heading i) := by
      have given := polar i
      change S (E.symm (E (P.edge i))) = _ at given
      rwa [E.symm_apply_apply, E.norm_map] at given
    have framed := K.framedIntrinsicRoll_edge_factor bank i
    rw [PolygonalChain.inComplexFrame_edge] at framed
    change (K.framedIntrinsicRoll bank).edge i =
      (K.projectedMetricStretch (bank.point i) : ℂ) * polarRay (e i) * S (P.edge i) at framed
    rw [K.framedIntrinsicRoll_edge, coord] at framed
    change (C.boundaryChainRoll bank).edge i = _
    apply mul_left_cancel₀ (polarRay_ne_zero phase)
    calc
      _ = (K.projectedMetricStretch (bank.point i) : ℂ) * polarRay (e i) *
          ((‖P.edge i‖ : ℂ) * polarRay (heading i)) := framed
      _ = (scale i : ℂ) * polarRay (e i + heading i) := by
        rw [polarRay_add]
        push_cast [scale]
        ring
      _ = polarRay phase * ((scale i : ℂ) * polarRay (h i)) := by
        rw [mul_comm (polarRay phase), mul_assoc, ← polarRay_add]
        congr 2
        dsimp only [h]
        ring
  have edge_cone (k : ℝ) (nonnegative : 0 ≤ k) (bounded : k ≤ opening) (i : Fin (n + 1)) :
      complexRotation k (R.chain.edge i) ∈ acuteBankCone center := by
    have close : |k + h i - center| < π / 4 := by
      rw [abs_lt]
      refine ⟨?_, ?_⟩ <;> dsimp only [center, width] at acute ⊢
      · linarith only [(between i).1, nonnegative, acute]
      · linarith only [(between i).2, bounded, acute]
    rw [polarized, complexRotation_apply]
    rw [show polarRay k * ((scale i : ℂ) * polarRay (h i)) =
        (scale i : ℂ) * polarRay (k + h i) by rw [polarRay_add]; ring]
    exact acuteBankCone.smul_mem (scale_nonneg i) (acuteBankCone.polarRay_mem close)
  refine ⟨center, ⟨fun i => ?_, ?_⟩, ⟨fun i => ?_, ?_⟩⟩
  · simpa only [complexRotation_apply, polarRay_zero, one_mul] using edge_cone 0 le_rfl opening_nonneg i
  · exact (show R.chain.edge (Fin.last n) ∈ _ from by
      simpa only [complexRotation_apply, polarRay_zero, one_mul] using edge_cone 0 le_rfl opening_nonneg (Fin.last n))
  · rw [R.rotateSuffix_zero_edge]
    exact edge_cone opening opening_nonneg le_rfl i
  · exact edge_cone opening opening_nonneg le_rfl (Fin.last n)

end ConvexRoof
end Unfoldings
