module

public import Unfoldings.Basic
public import Unfoldings.Geometry.RadialClosureSegments
public import Mathlib.Tactic.FinCases

/-! Literal three-link radial closures have only their actual prescribed corner contacts. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- The terminal, middle, and initial closing segments, with the genuine endpoint order. -/
def radialClosingLinks (q a b c : Plane) : Fin 3 → Plane × Plane := ![(b, c), (c, q), (q, a)]

/-- Actual geometric closing corners, with coincidences counted only once. -/
def radialClosingCorners (q a b c : Plane) : Finset Plane := by
  classical
  exact {a, b, q, c}

open Classical in
theorem radialClosingCorners_card_le (q a b c : Plane) :
    (radialClosingCorners q a b c).card ≤ 4 := by
  have first := Finset.card_insert_le a ({b, q, c} : Finset Plane)
  have second := Finset.card_insert_le b ({q, c} : Finset Plane)
  have third := Finset.card_insert_le q ({c} : Finset Plane)
  simp only [Finset.card_singleton] at third
  change ({a, b, q, c} : Finset Plane).card ≤ 4
  omega

/-- Strict radial and supporting-halfplane geometry makes each actual connector genuine. -/
theorem radialClosingLinks_different (q a b c : Plane) (initial : 0 < dist q a)
    (height : Plane →ₗ[ℝ] ℝ) (outside : height (c - q) < 0)
    (outward : 0 < inner ℝ (b - q) (c - b)) (i : Fin 3) :
    (radialClosingLinks q a b c i).1 ≠ (radialClosingLinks q a b c i).2 := by
  fin_cases i
  · intro same
    change b = c at same
    rw [same, sub_self, inner_zero_right] at outward
    exact lt_irrefl 0 outward
  · intro same
    change c = q at same
    rw [same, sub_self, map_zero] at outside
    exact lt_irrefl 0 outside
  · exact dist_pos.mp initial

open Classical in
/-- Radial separation restricts pairwise connector contacts to actual prescribed corners. -/
theorem radialClosingLinks_contacts (q a b c : Plane) (progress : dist q a < dist q b)
    (height : Plane →ₗ[ℝ] ℝ) (first : 0 ≤ height (a - q)) (last : 0 ≤ height (b - q))
    (outside : height (c - q) < 0) (outward : 0 < inner ℝ (b - q) (c - b)) :
    ∀ i j, i ≠ j → segment ℝ (radialClosingLinks q a b c i).1 (radialClosingLinks q a b c i).2 ∩
      segment ℝ (radialClosingLinks q a b c j).1 (radialClosingLinks q a b c j).2 ⊆
        (radialClosingCorners q a b c : Set Plane) := by
  have at_c {z : Plane} (one : z ∈ segment ℝ b c) (two : z ∈ segment ℝ c q) :
      z ∈ radialClosingCorners q a b c := by
    have on_other : z ∈ segment ℝ q c := (segment_symm ℝ c q) ▸ two
    have same := source_terminal_segments_inter height q b c last outside outward
    have equal := Set.mem_singleton_iff.mp ((Set.ext_iff.mp same z).mp ⟨on_other, one⟩)
    simp only [equal, radialClosingCorners, Finset.mem_insert, Finset.mem_singleton]
    simp
  have at_q {z : Plane} (one : z ∈ segment ℝ c q) (two : z ∈ segment ℝ q a) :
      z ∈ radialClosingCorners q a b c := by
    have on_other : z ∈ segment ℝ q c := (segment_symm ℝ c q) ▸ one
    have same := source_segments_inter height q a c first outside
    have equal := Set.mem_singleton_iff.mp ((Set.ext_iff.mp same z).mp ⟨two, on_other⟩)
    simp [equal, radialClosingCorners]
  have excluded {z : Plane} (one : z ∈ segment ℝ b c) (two : z ∈ segment ℝ q a) : False := by
    have upper := dist_initial_segment_le q a two
    have same := terminal_segment_inter_radial_disk q b c outward
    have equal := Set.mem_singleton_iff.mp ((Set.ext_iff.mp same z).mp
      ⟨one, upper.trans progress.le⟩)
    rw [equal] at upper
    exact not_le_of_gt progress upper
  intro i j different z member
  rcases member with ⟨one, two⟩
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (different rfl).elim
    | exact at_c one two
    | exact at_c two one
    | exact at_q one two
    | exact at_q two one
    | exact (excluded one two).elim
    | exact (excluded two one).elim

end Unfoldings
