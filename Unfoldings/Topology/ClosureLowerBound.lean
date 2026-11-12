module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.Constructions.SumProd

/-! Quantitative lower distance bounds pass to the full closure of a continuous map's domain. -/

@[expose] public section

namespace Unfoldings

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem lower_norm_bound_on_closure {S : Set E} {f : E → F} (continuous : Continuous f)
    (c K : ℝ) (bound : ∀ p ∈ S, ∀ q ∈ S, c * ‖q - p‖ ≤ K * ‖f q - f p‖) :
    ∀ p ∈ closure S, ∀ q ∈ closure S, c * ‖q - p‖ ≤ K * ‖f q - f p‖ := by
  let good : Set (E × E) := {z | c * ‖z.2 - z.1‖ ≤ K * ‖f z.2 - f z.1‖}
  have closed : IsClosed good := isClosed_le
    ((continuous_snd.sub continuous_fst).norm.const_mul c)
    (((continuous.comp continuous_snd).sub (continuous.comp continuous_fst)).norm.const_mul K)
  have inside : S ×ˢ S ⊆ good := fun _ member => bound _ member.1 _ member.2
  have extend := closure_minimal inside closed
  rw [closure_prod_eq] at extend
  intro p first q last
  exact extend (show (p, q) ∈ closure S ×ˢ closure S from ⟨first, last⟩)

theorem injOn_closure_of_lower_norm_bound {S : Set E} {f : E → F} (continuous : Continuous f)
    {c K : ℝ} (positive : 0 < c)
    (bound : ∀ p ∈ S, ∀ q ∈ S, c * ‖q - p‖ ≤ K * ‖f q - f p‖) :
    Set.InjOn f (closure S) := by
  intro p first q last equal
  have separation := lower_norm_bound_on_closure continuous c K bound p first q last
  rw [equal, sub_self, norm_zero, mul_zero] at separation
  have zero : ‖q - p‖ = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right separation positive) (norm_nonneg _)
  exact (sub_eq_zero.mp (norm_eq_zero.mp zero)).symm

end Unfoldings
