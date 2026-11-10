module

public import Unfoldings.Geometry.AngleMonotone
public import Unfoldings.Geometry.Shear

/-!
# Three acute sectors covering a backward halfplane

These algebraic near-quadrants have disjoint interiors. For a positive small
parameter all three are acute; their outer gap lies in the forward halfplane.
Their closed cones are stable under adding an outgoing strict-cone direction.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Positive coordinates in the upper, middle, and lower near-quadrants. -/
def threeSectorCoordinates (t : ℝ) (i : Fin 3) : Plane →ₗ[ℝ] Plane where
  toFun v := if i = 0 then WithLp.toLp 2 ![(1 - t) * v 0 + v 1,
      (1 - t) * v 1 - (1 + t) * v 0]
    else if i = 1 then WithLp.toLp 2 ![v 1 - (1 - t) * v 0, -v 1 - (1 - t) * v 0]
    else WithLp.toLp 2 ![-(1 + t) * v 0 - (1 - t) * v 1, (1 - t) * v 0 - v 1]
  map_add' v w := by
    split_ifs <;> ext j <;> fin_cases j <;> simp <;> ring
  map_smul' r v := by
    split_ifs <;> ext j <;> fin_cases j <;> simp <;> ring

def closedThreeSector (t : ℝ) (i : Fin 3) : Set Plane :=
  {v | 0 ≤ threeSectorCoordinates t i v 0 ∧ 0 ≤ threeSectorCoordinates t i v 1}

def strictThreeSector (t : ℝ) (i : Fin 3) : Set Plane :=
  {v | StrictQuadrant (threeSectorCoordinates t i v)}

theorem strictThreeSector_subset_closed (t : ℝ) (i : Fin 3) :
    strictThreeSector t i ⊆ closedThreeSector t i := fun _ h => ⟨h.1.le, h.2.le⟩

/-- Distinct sector closures can share rays; a strict sector never meets another closure. -/
theorem strictThreeSector_disjoint_closed {t : ℝ} (nonnegative : 0 ≤ t) (small : t < 1) :
    Pairwise (fun i j : Fin 3 => Disjoint (strictThreeSector t i) (closedThreeSector t j)) := by
  intro i j different
  apply Set.disjoint_left.mpr
  intro v hi hj
  fin_cases i <;> fin_cases j <;>
    norm_num [strictThreeSector, StrictQuadrant, closedThreeSector,
      threeSectorCoordinates] at hi hj different
  all_goals nlinarith [mul_pos (by linarith : 0 < 1 - t) (by linarith : 0 < 1 + t)]

/-- Every backward direction belongs to at least one of the three closed near-quadrants. -/
theorem mem_closedThreeSector_of_backward {t : ℝ} (nonnegative : 0 ≤ t) (small : t < 1)
    {v : Plane} (backward : v 0 ≤ 0) : ∃ i : Fin 3, v ∈ closedThreeSector t i := by
  by_cases upper : 0 ≤ (1 - t) * v 0 + v 1
  · refine ⟨0, ?_⟩
    change 0 ≤ (1 - t) * v 0 + v 1 ∧ 0 ≤ (1 - t) * v 1 - (1 + t) * v 0
    have y : 0 ≤ v 1 := by nlinarith
    exact ⟨upper, sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos (by linarith) backward).trans
      (mul_nonneg (by linarith) y))⟩
  · by_cases lower : 0 ≤ (1 - t) * v 0 - v 1
    · refine ⟨2, ?_⟩
      change 0 ≤ -(1 + t) * v 0 - (1 - t) * v 1 ∧ 0 ≤ (1 - t) * v 0 - v 1
      have y : v 1 ≤ 0 := by nlinarith
      exact ⟨sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos (by linarith) y).trans
        (mul_nonneg_of_nonpos_of_nonpos (by linarith) backward)), lower⟩
    · refine ⟨1, ?_⟩
      change 0 ≤ v 1 - (1 - t) * v 0 ∧ 0 ≤ -v 1 - (1 - t) * v 0
      constructor <;> linarith

/-- A deterministic label on the covered halfplane; unused exterior points get the last label. -/
def threeSectorLabel (t : ℝ) (p : Plane) : Fin 3 := by
  classical
  exact if p ∈ closedThreeSector t 0 then 0 else if p ∈ closedThreeSector t 1 then 1 else 2

theorem threeSectorLabel_eq_of_strict {t : ℝ} (nonnegative : 0 ≤ t) (small : t < 1)
    {p : Plane} {i : Fin 3} (inside : p ∈ strictThreeSector t i) : threeSectorLabel t p = i := by
  classical
  have own := strictThreeSector_subset_closed t i inside
  have different (j : Fin 3) (ne : i ≠ j) : p ∉ closedThreeSector t j :=
    fun other => Set.disjoint_left.mp
      (strictThreeSector_disjoint_closed nonnegative small ne) inside other
  fin_cases i
  · exact ite_eq_left own
  · change p ∈ closedThreeSector t 1 at own
    change threeSectorLabel t p = 1
    rw [threeSectorLabel, ite_eq_right (different 0 (by decide)), ite_eq_left own]
  · change threeSectorLabel t p = 2
    rw [threeSectorLabel, ite_eq_right (different 0 (by decide)),
      ite_eq_right (different 1 (by decide))]

theorem mem_closedThreeSector_label_of_backward {t : ℝ} (nonnegative : 0 ≤ t) (small : t < 1)
    {p : Plane} (backward : p 0 ≤ 0) : p ∈ closedThreeSector t (threeSectorLabel t p) := by
  classical
  obtain ⟨i, hi⟩ := mem_closedThreeSector_of_backward nonnegative small backward
  unfold threeSectorLabel
  split_ifs with first second
  · exact first
  · exact second
  · fin_cases i
    · exact (first hi).elim
    · exact (second hi).elim
    · exact hi

/-- Addition preserves the sector and moves its endpoint into the strict interior. -/
theorem add_mem_strictThreeSector {t : ℝ} {i : Fin 3} {p d : Plane}
    (position : p ∈ closedThreeSector t i) (direction : d ∈ strictThreeSector t i) :
    p + d ∈ strictThreeSector t i := by
  change 0 < threeSectorCoordinates t i (p + d) 0 ∧
    0 < threeSectorCoordinates t i (p + d) 1
  rw [map_add]
  exact ⟨add_pos_of_nonneg_of_pos position.1 direction.1,
    add_pos_of_nonneg_of_pos position.2 direction.2⟩

/-- Outgoing steps preserve the source-centered sector label, even when the start is on a bank. -/
theorem threeSectorLabel_add {t : ℝ} (nonnegative : 0 ≤ t) (small : t < 1)
    {p d : Plane} (position : p ∈ closedThreeSector t (threeSectorLabel t p))
    (direction : d ∈ strictThreeSector t (threeSectorLabel t p)) :
    threeSectorLabel t (p + d) = threeSectorLabel t p :=
  threeSectorLabel_eq_of_strict nonnegative small (add_mem_strictThreeSector position direction)

end Unfoldings
