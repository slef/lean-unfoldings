module

public import Unfoldings.Geometry.PolygonalChain
public import Unfoldings.Cone.Sector
public import Mathlib.Algebra.BigOperators.Fin

/-! Construct finite chains from edge vectors and from actual lengths and unreduced headings. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] {n : ℕ}

def ofEdges (origin : E) (steps : Fin n → E) : PolygonalChain E n where
  vertex i := origin + Fin.partialSum steps i

@[simp] theorem ofEdges_start (origin : E) (steps : Fin n → E) :
    (ofEdges origin steps).vertex 0 = origin := by simp [ofEdges]

@[simp] theorem ofEdges_edge (origin : E) (steps : Fin n → E) (i : Fin n) :
    (ofEdges origin steps).edge i = steps i := by
  simp only [edge, ofEdges, Fin.partialSum_succ]
  abel

def ofHeadings (origin : ℂ) (length heading : Fin n → ℝ) : PolygonalChain ℂ n :=
  ofEdges origin (fun i => (length i : ℂ) * polarRay (heading i))

@[simp] theorem ofHeadings_start (origin : ℂ) (length heading : Fin n → ℝ) :
    (ofHeadings origin length heading).vertex 0 = origin := by simp [ofHeadings]

@[simp] theorem ofHeadings_edge (origin : ℂ) (length heading : Fin n → ℝ) (i : Fin n) :
    (ofHeadings origin length heading).edge i = (length i : ℂ) * polarRay (heading i) :=
  ofEdges_edge _ _ _

/-- A nonnegative opening budget controls every prefix, rather than each summand separately. -/
theorem partialSum_bounds (weight : Fin n → ℝ) (nonnegative : ∀ i, 0 ≤ weight i)
    (j : Fin (n + 1)) : 0 ≤ Fin.partialSum weight j ∧
      Fin.partialSum weight j ≤ ∑ i, weight i := by
  have monotone : Monotone (Fin.partialSum weight) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    rw [Fin.partialSum_succ]
    exact le_add_of_nonneg_right (nonnegative i)
  have first := monotone (show (0 : Fin (n + 1)) ≤ j from Nat.zero_le j.val)
  have last := monotone (Fin.le_last j)
  have total : Fin.partialSum weight (Fin.last n) = ∑ i, weight i := by
    change ((List.ofFn weight).take n).sum = ∑ i, weight i
    rw [List.take_of_length_le (by simp only [List.length_ofFn]; exact le_rfl), List.sum_ofFn]
  simpa only [Fin.partialSum_zero, total] using And.intro first last

end Unfoldings.PolygonalChain
