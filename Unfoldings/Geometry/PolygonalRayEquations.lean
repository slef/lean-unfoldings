module

public import Unfoldings.Geometry.PolygonalRay
public import Unfoldings.Geometry.ComplexLineEquation

/-! Finite proper affine supports cover polygonal banks and their actual infinite ends. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n)

def equations : Set (ℂ →ᵃ[ℝ] ℝ) :=
  Set.range (fun i : Fin n => complexLineEquation (R.chain.vertex i.castSucc)
    (R.chain.vertex i.succ)) ∪
    {complexLineEquation R.start R.start,
      complexLineEquation (R.chain.vertex (Fin.last n)) (R.chain.vertex (Fin.last n) + R.direction)}

theorem finite_equations : R.equations.Finite :=
  (Set.finite_range _).union (Set.toFinite _)

theorem equations_ne_zero (l : ℂ →ᵃ[ℝ] ℝ) (member : l ∈ R.equations) : l ≠ 0 := by
  rcases member with ⟨i, rfl⟩ | root | last
  · exact complexLineEquation_ne_zero _ _
  · subst l
    exact complexLineEquation_ne_zero _ _
  · subst l
    exact complexLineEquation_ne_zero _ _

/-- Every point lies on one of the constructed proper supporting lines. -/
theorem equations_cover (z : ℂ) (member : z ∈ R.carrier) : ∃ l ∈ R.equations, l z = 0 := by
  rcases member with finite | ⟨t, rfl⟩
  · have cover := R.chain.path_range.subset finite
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at cover
    rcases cover with root | ⟨i, t, rfl⟩
    · have same : z = R.start := Set.mem_singleton_iff.mp root
      refine ⟨complexLineEquation R.start R.start, Or.inr (Or.inl rfl), ?_⟩
      rw [same, complexLineEquation_first]
    · exact ⟨complexLineEquation (R.chain.vertex i.castSucc) (R.chain.vertex i.succ),
        Or.inl ⟨i, rfl⟩, complexLineEquation_lineMap _ _ _⟩
  · refine ⟨complexLineEquation (R.chain.vertex (Fin.last n))
      (R.chain.vertex (Fin.last n) + R.direction), Or.inr (Or.inr rfl), ?_⟩
    rw [R.tail_lineMap]
    exact complexLineEquation_lineMap _ _ _

end Unfoldings.PolygonalRay
