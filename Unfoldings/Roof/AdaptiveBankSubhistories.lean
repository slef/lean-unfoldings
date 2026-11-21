module

public import Unfoldings.Roof.AdaptiveAnchoredHistories
public import Unfoldings.Roof.SharpBankSubhistories

/-! Sharp real developments of the banks of an actual adaptive forest. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Real

universe u v w z

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {L : Set Plane} {r margin η : ℝ}
  (R : K.CompatibleAdaptiveRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary L r margin η)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (positive : 0 < r) (disk : Metric.closedBall (0 : Plane) r ⊆ L)
  {b : ℝ} (bound_pos : 0 < b) (ratio : r ≤ b) (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)

local notation "R₀" => R.asCommonPotentialRouting positive disk bound_pos ratio upper

include no_boundary in
/-- A physical bank may be subdivided by any conforming mesh. Its route yields the
certified radial and length bounds on all subhistories of the actual developed roll. -/
theorem adaptive_bank_subhistories
    {Fine : Type w} [Fintype Fine] {D : TriangleComplex.{w, z} Fine} (Q : ConvexRoof D)
    {φ γ A : ℝ} (tilt_pos : 0 < φ) (small_phi : φ < π / 2)
    (height_bound : (3 : ℝ) / 4 ≤ cos φ) (tilt : Q.TiltBound φ)
    (gamma_pos : 0 < γ) (gamma_le : γ ≤ 1) (interior_margin : γ ≤ margin)
    (exterior_margin : γ ≤ η) (length_bound : b / r ≤ A)
    {retain : Set D.Seam} {n : ℕ} (bank : (D.boundarySystem retain).Chain n)
    (cut : ∀ i, ¬ D.IsBoundaryEdge Set.univ (D.germEdge (bank.point i).val))
    (follows : (R₀).Follows (Q.folding.projectedBoundaryChain bank))
    (small : radialBlockError (cos φ)⁻¹ (shallowDevelopmentHeading φ) A
      (sqrt (1 - γ ^ 2)) π < γ) :
    let E := radialBlockError (cos φ)⁻¹ (shallowDevelopmentHeading φ) A (sqrt (1 - γ ^ 2)) π
    let D' := (cos φ)⁻¹ * A / (1 - E)
    let d := (γ - E) / (1 + E)
    let P := D.boundaryChainRoll bank
    (∀ (first length : ℕ) (fits : first + length ≤ n + 1),
      let interval := P.interval first length fits
      interval.projectedLength ≤ D' * ‖interval.vertex (Fin.last length) - interval.vertex 0‖) ∧
    ∀ (j : Fin (n + 2)) (i : Fin (n + 1)), j.val ≤ i.val →
      d * (‖P.vertex i.castSucc - P.vertex j‖ * ‖P.edge i‖) ≤
        inner ℝ (P.vertex i.castSucc - P.vertex j) (P.edge i) := by
  have length_nonneg := (div_nonneg bound_pos.le positive.le).trans length_bound
  apply Q.sharp_physical_bank_subhistories tilt_pos small_phi height_bound tilt gamma_pos
    gamma_le length_nonneg bank cut _ _ small
  · exact commonFollows_adaptive_radial_margin compact nonempty R no_boundary positive
      disk bound_pos ratio upper (Q.folding.projectedBoundaryChain bank) follows
      (Q.projectedBoundaryChain_edge_ne_zero bank) gamma_pos.le gamma_le
      interior_margin exterior_margin
  · dsimp only
    intro first length fits
    let A' := (Q.folding.projectedBoundaryChain bank).interval first length fits
    have routes : (R₀).Follows A' := fun i => follows ⟨first + i.val, by omega⟩
    exact (R.commonFollows_length_bound positive disk bound_pos ratio upper A' routes).trans
      (mul_le_mul_of_nonneg_right length_bound (norm_nonneg _))

end Unfoldings.ConvexRoof
