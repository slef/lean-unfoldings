module

public import Unfoldings.Cap.GeometricBankTurnComparison
public import Unfoldings.Geometry.RadialClosingLinks
public import Unfoldings.Geometry.PolygonalClosureEquations

/-! Derived actual one-sided bank comparison for the radial three-segment closure. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {n : ℕ} (P : PolygonalChain Plane n) (q c : Plane)
  (jordan : Schoenflies.IsJordanCurve (P.threeSegmentClosure q c))
  (contains : P.threeSegmentClosure q c ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) (P.threeSegmentClosure q c))

include jordan contains avoids in
open Classical in
/-- Actual closure geometry gives the bank error Ω + 6φ + 8πε with no assumed turn budget. -/
theorem abs_radial_bank_turn_error_le
    (inside : P.threeSegmentClosure q c ⊆ interior K.footprint)
    (initial : 0 < dist q (P.vertex 0))
    (progress : dist q (P.vertex 0) < dist q (P.vertex (Fin.last n)))
    (height : Plane →ₗ[ℝ] ℝ) (first : 0 ≤ height (P.vertex 0 - q))
    (last : 0 ≤ height (P.vertex (Fin.last n) - q)) (outside : height (c - q) < 0)
    (outward : 0 < inner ℝ (P.vertex (Fin.last n) - q) (c - P.vertex (Fin.last n)))
    {ε φ : ℝ} (error_nonnegative : 0 ≤ ε) (error : K.RelativeCornerAngleError ε)
    (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    |∑ i ∈ K.jordanGeometricBankIndices jordan contains avoids (Set.range P.path)
        (radialClosingCorners q (P.vertex 0) (P.vertex (Fin.last n)) c),
      K.jordanContourTurnError jordan contains avoids i| ≤
        C.totalInteriorAngularDefect Set.univ + 6 * φ + 8 * Real.pi * ε := by
  let a := P.vertex 0
  let b := P.vertex (Fin.last n)
  let links := radialClosingLinks q a b c
  have cover : P.threeSegmentClosure q c ⊆ Set.range P.path ∪
      ⋃ k : Fin 3, segment ℝ (links k).1 (links k).2 := by
    intro x member
    rcases member with bank | ((terminal | middle) | initial)
    · exact Or.inl bank
    · exact Or.inr (Set.mem_iUnion.mpr ⟨0, terminal⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨1, middle⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨2, initial⟩)
  have bound := K.abs_jordan_geometric_bank_error_le jordan contains avoids inside
    (Set.range P.path) (isCompact_range P.path.continuous).isClosed links
    (radialClosingLinks_different q a b c initial height outside outward)
    (radialClosingCorners q a b c) cover
    (radialClosingLinks_contacts q a b c progress height first last outside outward)
    error_nonnegative error nonnegative small tilt
  have card_bound : ((radialClosingCorners q a b c).card : ℝ) ≤ 4 :=
    Nat.cast_le.mpr (radialClosingCorners_card_le q a b c)
  have delta_nonnegative : 0 ≤ ε * (2 * Real.pi) := mul_nonneg error_nonnegative (by positivity)
  have corners := mul_le_mul_of_nonneg_right card_bound delta_nonnegative
  norm_num only [Nat.cast_ofNat] at bound
  exact bound.trans (by nlinarith)

end Unfoldings.ConvexCap
