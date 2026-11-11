module

public import Unfoldings.Geometry.ChainHeightCover
public import Unfoldings.Geometry.BankRadialOrder
public import Unfoldings.Geometry.StrictHeightGraphs

/-! Exact height graphs of strictly coordinate-increasing chains retain strict progress. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain ℂ n)

/-- A strict linear coordinate is injective on the whole chain, irrespective of how its
two points are represented at shared edge endpoints. -/
theorem point_eq_of_strict_linear_eq (height : ℂ →ₗ[ℝ] ℝ)
    (positive : ∀ i, 0 < height (P.edge i)) (i j : Fin n) (s r : unitInterval)
    (equal : height (P.point i s) = height (P.point j r)) : P.point i s = P.point j r := by
  rcases before_total i j s r with ordered | ordered
  · exact P.point_eq_of_linear_eq height positive i j s r ordered equal
  · exact (P.point_eq_of_linear_eq height positive j i r s ordered equal.symm).symm

/-- Only the represented height range is claimed. An arbitrary total graph extension past
the last chain vertex need not have strict physical coordinates. -/
theorem heightGraph_strictCoordinatesOn (G : MonotoneHeightGraph)
    (representation : ∀ i (s : unitInterval),
      G.coordinate ((P.point i s).re + (P.point i s).im) = (P.point i s).re)
    (positive : ∀ i, 0 < (P.edge i).re ∧ 0 < (P.edge i).im) :
    G.StrictCoordinatesOn (Set.Ico ((P.vertex 0).re + (P.vertex 0).im)
      ((P.vertex (Fin.last n)).re + (P.vertex (Fin.last n)).im)) := by
  have locate := P.heightGraph_point_on_chain G representation
    (fun i => add_pos (positive i).1 (positive i).2)
  have injective_coordinate (height : ℂ →ₗ[ℝ] ℝ)
      (steps : ∀ i, 0 < height (P.edge i)) {a b : ℝ}
      (ha : a ∈ Set.Ico ((P.vertex 0).re + (P.vertex 0).im)
        ((P.vertex (Fin.last n)).re + (P.vertex (Fin.last n)).im))
      (hb : b ∈ Set.Ico ((P.vertex 0).re + (P.vertex 0).im)
        ((P.vertex (Fin.last n)).re + (P.vertex (Fin.last n)).im))
      (equal : height (G.point a) = height (G.point b)) : a = b := by
    obtain ⟨i, s, first⟩ := locate a ha.1 ha.2
    obtain ⟨j, r, last⟩ := locate b hb.1 hb.2
    have same := P.point_eq_of_strict_linear_eq height steps i j s r
      (by rwa [← first, ← last])
    exact G.point_injective (first.trans (same.trans last.symm))
  constructor
  · intro a ha b hb ordered
    refine lt_of_le_of_ne (G.coordinate_mono ordered.le) ?_
    intro equal
    exact ordered.ne (injective_coordinate Complex.reCLM.toLinearMap
      (fun i => (positive i).1) ha hb equal)
  · intro a ha b hb ordered
    refine lt_of_le_of_ne (G.complement_mono ordered.le) ?_
    intro equal
    exact ordered.ne (injective_coordinate Complex.imCLM.toLinearMap
      (fun i => (positive i).2) ha hb equal)

end Unfoldings.PolygonalChain
