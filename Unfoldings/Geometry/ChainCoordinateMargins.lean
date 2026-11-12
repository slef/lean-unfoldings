module

public import Unfoldings.Geometry.ChainLinear
public import Unfoldings.Geometry.BankRadialOrder

/-! Uniform coordinate margins of chain edges pass to arbitrary height-ordered chain points. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain ℂ n)

/-- Subtracting a multiple of total height turns each margin into an ordinary linear order. -/
theorem coordinate_increment_margins {μ : ℝ}
    (heights : ∀ i, 0 ≤ (P.edge i).re + (P.edge i).im)
    (margins : ∀ i,
      μ * ((P.edge i).re + (P.edge i).im) ≤ (P.edge i).re ∧
      μ * ((P.edge i).re + (P.edge i).im) ≤ (P.edge i).im)
    (i j : Fin n) (s r : unitInterval)
    (ordered : (P.point i s).re + (P.point i s).im <
      (P.point j r).re + (P.point j r).im) :
    μ * (((P.point j r).re + (P.point j r).im) -
      ((P.point i s).re + (P.point i s).im)) ≤ (P.point j r).re - (P.point i s).re ∧
    μ * (((P.point j r).re + (P.point j r).im) -
      ((P.point i s).re + (P.point i s).im)) ≤ (P.point j r).im - (P.point i s).im := by
  let height : ℂ →ₗ[ℝ] ℝ := Complex.reCLM.toLinearMap + Complex.imCLM.toLinearMap
  have height_mono := (P.monotone_linear_vertices_iff height).mpr heights
  have before : Before i s j r := by
    rcases before_total i j s r with forward | backward
    · exact forward
    · have reverse := P.linear_point_le height height_mono j i r s backward
      exact (not_le_of_gt ordered reverse).elim
  have margin_order (coordinate : ℂ →ₗ[ℝ] ℝ)
      (edge_bound : ∀ i, μ * height (P.edge i) ≤ coordinate (P.edge i)) :
      μ * (height (P.point j r) - height (P.point i s)) ≤
        coordinate (P.point j r) - coordinate (P.point i s) := by
    let excess : ℂ →ₗ[ℝ] ℝ := coordinate - μ • height
    have excess_mono := (P.monotone_linear_vertices_iff excess).mpr (fun i => by
      change 0 ≤ coordinate (P.edge i) - μ * height (P.edge i)
      exact sub_nonneg.mpr (edge_bound i))
    have progress := P.linear_point_le excess excess_mono i j s r before
    change coordinate (P.point i s) - μ * height (P.point i s) ≤
      coordinate (P.point j r) - μ * height (P.point j r) at progress
    linarith
  exact ⟨margin_order Complex.reCLM.toLinearMap (fun i => (margins i).1),
    margin_order Complex.imCLM.toLinearMap (fun i => (margins i).2)⟩

end Unfoldings.PolygonalChain
