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

/-- The bisector of the hull of a stem interval and its terminal direction
controls every refined edge of the same-sign history. -/
theorem exists_threeExit_history_axis {E : Type*} (headings : E → ℂ) (terminal : ℂ)
    {lo hi A : ℝ} (term_ne : terminal ≠ 0)
    (span : max hi terminal.arg - min lo terminal.arg ≤ A)
    (steps : ∀ i, headings i ≠ 0 →
      (headings i).arg ∈ Set.Icc lo hi ∨ (headings i).arg = terminal.arg) :
    ∃ axis : ℂ, ‖axis‖ = 1 ∧ angle axis terminal ≤ A / 2 ∧
      ∀ i, headings i ≠ 0 → angle axis (headings i) ≤ A / 2 := by
  let l := min lo terminal.arg
  let h := max hi terminal.arg
  have terminal_mem : terminal.arg ∈ Set.Icc l h :=
    ⟨min_le_right _ _, le_max_right _ _⟩
  have stems_mem : Set.Icc lo hi ⊆ Set.Icc l h :=
    Set.Icc_subset_Icc (min_le_left _ _) (le_max_left _ _)
  have halfSpan : (h - l) / 2 ≤ A / 2 :=
    div_le_div_of_nonneg_right span (by norm_num)
  refine ⟨polarRay ((l + h) / 2), norm_polarRay _,
    (deviation_from_interval_midpoint term_ne terminal_mem).trans halfSpan, ?_⟩
  intro i genuine
  apply le_trans _ halfSpan
  apply deviation_from_interval_midpoint genuine
  rcases steps i genuine with stem | straight
  · exact stems_mem stem
  · exact straight.symm ▸ terminal_mem

/-- Every block of a same-sign history satisfies the length and radial bounds.
The terminal ray may account for any number of refined mesh edges. -/
theorem threeExit_history_bounds {n : ℕ} (P : PolygonalChain ℂ n) (terminal : ℂ)
    {lo hi A : ℝ} (aperture : A ≤ π / 2) (term_ne : terminal ≠ 0)
    (span : max hi terminal.arg - min lo terminal.arg ≤ A)
    (steps : ∀ i, P.edge i ≠ 0 →
      (P.edge i).arg ∈ Set.Icc lo hi ∨ (P.edge i).arg = terminal.arg)
    (j : Fin (n + 1)) (i : Fin n) (earlier : j.val ≤ i.val) :
    let L := (P.interval j.val (i.val - j.val) (by omega)).projectedLength
    let chord := P.vertex i.castSucc - P.vertex j
    L ≤ √2 * ‖chord‖ ∧
      cos A * (‖chord‖ * ‖P.edge i‖) ≤ inner ℝ chord (P.edge i) := by
  obtain ⟨axis, unit, _, heading⟩ :=
    exists_threeExit_history_axis P.edge terminal term_ne span steps
  have nonnegative : 0 ≤ A / 2 := by
    linarith only [span, min_le_right lo terminal.arg, le_max_right hi terminal.arg]
  have narrow : A / 2 ≤ π / 4 := by linarith only [aperture]
  have bounds := P.cone_subpath_bounds unit nonnegative narrow heading j i earlier
  have width : 2 * (A / 2) = A := by ring
  simpa only [width] using bounds

end Unfoldings.FewestNets
