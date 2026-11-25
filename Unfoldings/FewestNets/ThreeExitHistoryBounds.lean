module

public import Unfoldings.Geometry.ConeHistoryBounds
public import Unfoldings.Geometry.PolarAngleBound

/-! Every same-sign history has one acute cone, determined by its eventual exit. -/

@[expose] public section

namespace Unfoldings.FewestNets

open InnerProductGeometry Real

private theorem deviation_from_interval_midpoint {z : ℂ} (nonzero : z ≠ 0)
    {lo hi : ℝ} (in_interval : z.arg ∈ Set.Icc lo hi) :
    angle (polarRay ((lo + hi) / 2)) z ≤ (hi - lo) / 2 := by
  have scaled : ‖z‖ • polarRay z.arg = z := by
    change (‖z‖ : ℂ) * polarRay z.arg = z
    exact Complex.norm_mul_exp_arg_mul_I z
  calc
    angle (polarRay ((lo + hi) / 2)) z =
        angle (polarRay ((lo + hi) / 2)) (‖z‖ • polarRay z.arg) :=
      congrArg (angle (polarRay ((lo + hi) / 2))) scaled.symm
    _ = angle (polarRay ((lo + hi) / 2)) (polarRay z.arg) :=
      angle_smul_right_of_pos _ _ (norm_pos_iff.mpr nonzero)
    _ ≤ |z.arg - (lo + hi) / 2| :=
      angle_polarRay_le_abs_sub ((lo + hi) / 2) z.arg
    _ ≤ _ := abs_le.mpr ⟨by linarith only [in_interval.1], by linarith only [in_interval.2]⟩

/-- An east-assigned path uses northeast stems and one terminal direction
near either east or north. Its full interval has width at most
`π / 2 - δ + ε`. West-assigned paths use the reflected coordinates. -/
theorem exists_threeExit_history_axis {E : Type*} (headings : E → ℂ) (terminal : ℂ)
    {δ ε : ℝ} (positive : 0 < δ) (δ_upper : δ ≤ π / 4)
    (ε_nonneg : 0 ≤ ε) (ε_lt : ε < δ) (term_ne : terminal ≠ 0)
    (steps : ∀ i, headings i ≠ 0 →
      (headings i).arg ∈ Set.Icc δ (π / 2 - δ) ∨ (headings i).arg = terminal.arg)
    (exit : terminal.arg ∈ Set.Icc (-ε) ε ∨
      terminal.arg ∈ Set.Icc (π / 2 - ε) (π / 2 + ε)) :
    ∃ axis : ℂ, ‖axis‖ = 1 ∧ angle axis terminal ≤ (π / 2 - δ + ε) / 2 ∧
      ∀ i, headings i ≠ 0 → angle axis (headings i) ≤ (π / 2 - δ + ε) / 2 := by
  obtain ⟨lo, hi, width, terminal_mem, stems_mem⟩ :
      ∃ lo hi : ℝ, hi - lo = π / 2 - δ + ε ∧ terminal.arg ∈ Set.Icc lo hi ∧
        Set.Icc δ (π / 2 - δ) ⊆ Set.Icc lo hi := by
    rcases exit with east | north
    · refine ⟨-ε, π / 2 - δ, by ring,
        ⟨east.1, east.2.trans (by linarith only [δ_upper, ε_lt])⟩, ?_⟩
      exact Set.Icc_subset_Icc (by linarith only [positive, ε_nonneg]) le_rfl
    · refine ⟨δ, π / 2 + ε, by ring,
        ⟨(by linarith only [δ_upper, ε_lt] : δ ≤ π / 2 - ε).trans north.1, north.2⟩, ?_⟩
      exact Set.Icc_subset_Icc le_rfl (by linarith only [positive, ε_nonneg])
  refine ⟨polarRay ((lo + hi) / 2), norm_polarRay _, ?_, ?_⟩
  · rw [← width]
    exact deviation_from_interval_midpoint term_ne terminal_mem
  · intro i genuine
    rw [← width]
    apply deviation_from_interval_midpoint genuine
    rcases steps i genuine with stem | straight
    · exact stems_mem stem
    · rw [straight]
      exact terminal_mem

/-- Every block of a same-sign history satisfies the length and radial bounds.
The terminal ray may account for any number of refined mesh edges. -/
theorem threeExit_history_bounds {n : ℕ} (P : PolygonalChain ℂ n) (terminal : ℂ)
    {δ ε : ℝ} (positive : 0 < δ) (δ_upper : δ ≤ π / 4)
    (ε_nonneg : 0 ≤ ε) (ε_lt : ε < δ) (term_ne : terminal ≠ 0)
    (steps : ∀ i, P.edge i ≠ 0 →
      (P.edge i).arg ∈ Set.Icc δ (π / 2 - δ) ∨ (P.edge i).arg = terminal.arg)
    (exit : terminal.arg ∈ Set.Icc (-ε) ε ∨
      terminal.arg ∈ Set.Icc (π / 2 - ε) (π / 2 + ε))
    (j : Fin (n + 1)) (i : Fin n) (earlier : j.val ≤ i.val) :
    let L := (P.interval j.val (i.val - j.val) (by omega)).projectedLength
    let chord := P.vertex i.castSucc - P.vertex j
    L ≤ √2 * ‖chord‖ ∧
      cos (π / 2 - δ + ε) * (‖chord‖ * ‖P.edge i‖) ≤ inner ℝ chord (P.edge i) := by
  obtain ⟨axis, unit, _, heading⟩ :=
    exists_threeExit_history_axis P.edge terminal positive δ_upper ε_nonneg ε_lt term_ne steps exit
  have nonnegative : 0 ≤ (π / 2 - δ + ε) / 2 := by
    linarith only [δ_upper, ε_nonneg, pi_pos]
  have narrow : (π / 2 - δ + ε) / 2 ≤ π / 4 := by linarith only [ε_lt]
  have bounds := P.cone_subpath_bounds unit nonnegative narrow heading j i earlier
  have width : 2 * ((π / 2 - δ + ε) / 2) = π / 2 - δ + ε := by ring
  simpa only [width] using bounds

end Unfoldings.FewestNets
