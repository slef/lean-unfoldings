module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Mesh-independent turning of secants to a concave real function

Secant slopes along any increasing partition are antitone. Their real arctangent
headings have total variation equal to the difference of the endpoint headings,
so a uniform slope bound controls all turns independently of partition size.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- The genuine real inclination of one secant, without angle reduction modulo a full turn. -/
def secantHeading {n : ℕ} (f : ℝ → ℝ) (time : Fin (n + 2) → ℝ) (i : Fin (n + 1)) : ℝ :=
  Real.arctan ((f (time i.succ) - f (time i.castSucc)) / (time i.succ - time i.castSucc))

theorem secantHeading_antitone {n : ℕ} {f : ℝ → ℝ} (concave : ConcaveOn ℝ Set.univ f)
    (time : Fin (n + 2) → ℝ) (ordered : StrictMono time) :
    Antitone (secantHeading f time) := by
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  have first := ordered (show i.castSucc.castSucc < i.castSucc.succ from Fin.castSucc_lt_succ)
  have last := ordered (show i.succ.castSucc < i.succ.succ from Fin.castSucc_lt_succ)
  simp only [Fin.succ_castSucc] at first
  exact Real.arctan_strictMono.monotone
    (concave.slope_anti_adjacent (Set.mem_univ _) (Set.mem_univ _) first last)

/-- Finite total variation of an antitone real sequence telescopes exactly. -/
theorem sum_abs_succ_sub_of_antitone {n : ℕ} (heading : Fin (n + 1) → ℝ)
    (ordered : Antitone heading) :
    (∑ i : Fin n, |heading i.succ - heading i.castSucc|) =
      heading 0 - heading (Fin.last n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have previous_sum := ih (fun i => heading i.castSucc) (fun i j le => ordered (by exact le))
    change (∑ i : Fin n, |heading i.succ.castSucc - heading i.castSucc.castSucc|) +
      |heading (Fin.last (n + 1)) - heading (Fin.last n).castSucc| = _
    rw [previous_sum, abs_of_nonpos (sub_nonpos.mpr (ordered (Fin.le_last _)))]
    change heading 0 - heading (Fin.last n).castSucc +
      -(heading (Fin.last (n + 1)) - heading (Fin.last n).castSucc) = _
    ring

/-- Concavity turns a local slope bound into one bound for every finite partition. -/
theorem sum_secantHeading_turn_le {n : ℕ} {f : ℝ → ℝ}
    (concave : ConcaveOn ℝ Set.univ f) (time : Fin (n + 2) → ℝ) (ordered : StrictMono time)
    {R : ℝ} (bound : ∀ i : Fin (n + 1),
      |(f (time i.succ) - f (time i.castSucc)) / (time i.succ - time i.castSucc)| ≤ R) :
    (∑ i : Fin n, |secantHeading f time i.succ - secantHeading f time i.castSucc|) ≤
      2 * Real.arctan R := by
  rw [sum_abs_succ_sub_of_antitone _ (secantHeading_antitone concave time ordered)]
  have first := Real.arctan_strictMono.monotone (abs_le.mp (bound 0)).2
  have last := Real.arctan_strictMono.monotone (abs_le.mp (bound (Fin.last n))).1
  rw [Real.arctan_neg] at last
  change secantHeading f time 0 ≤ Real.arctan R at first
  change -Real.arctan R ≤ secantHeading f time (Fin.last n) at last
  linarith

end Unfoldings
