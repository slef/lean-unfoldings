module

public import Unfoldings.Metric.PolygonalCut

/-! Away from the actual cut, physical folding uniquely specifies the metric copy. -/

@[expose] public section

namespace Unfoldings.MetricGluing

variable {E I : Type*} [NormedAddCommGroup E] [Finite I]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i)) (cuts : Set E)

/-- Arbitrary cut-metric points with equal uncut physical positions are the same metric point. -/
theorem cut_eq_of_fold_eq_outside (x y : PolygonalCut cells closed cuts)
    (same : (cutSeams cells closed cuts).fold x = (cutSeams cells closed cuts).fold y)
    (outside : (cutSeams cells closed cuts).fold x ∉ cuts) : x = y := by
  obtain ⟨a, rfl⟩ := point_surjective (fun i => cells i) (cutSeams cells closed cuts).relation x
  obtain ⟨b, rfl⟩ := point_surjective (fun i => cells i) (cutSeams cells closed cuts).relation y
  exact cutSeams_point_eq_of_physical_eq cells closed cuts same outside

end Unfoldings.MetricGluing
