module

public import Unfoldings.Geometry.RadialChainPoints

/-! Whole-point radial order is equivalent to the finite outward tests at original vertices. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n)

/-- Whole-point radial order recovers every original vertex-to-edge outward test. -/
theorem GloballyRadiallyMonotone.outward (radial : P.GloballyRadiallyMonotone) : P.Outward := by
  apply P.radiallyMonotone_iff_outward.mp
  intro j i earlier t s ordered
  let k : Fin n := ⟨j.val, lt_of_le_of_lt earlier i.isLt⟩
  have anchor : P.point k 0 = P.vertex j := by
    rw [P.point_zero]
    exact congrArg P.vertex (Fin.ext rfl)
  have before : Before k 0 i t := by
    rcases lt_or_eq_of_le (show k ≤ i from earlier) with less | same
    · exact Or.inl less
    · exact Or.inr ⟨same, t.property.1⟩
  have estimate := radial k i i 0 t s before (Or.inr ⟨rfl, ordered⟩)
  simpa only [anchor] using estimate

/-- The finite tests and the condition on arbitrary ordered points have exactly the same meaning. -/
theorem globallyRadiallyMonotone_iff_outward : P.GloballyRadiallyMonotone ↔ P.Outward :=
  ⟨GloballyRadiallyMonotone.outward P, Outward.globallyRadiallyMonotone P⟩

end Unfoldings.PolygonalChain
