module

public import Unfoldings.Metric.Gluing
public import Mathlib.Topology.MetricSpace.Isometry

/-! Compatible isometric cell maps rule out intrinsic shortcuts inside a cell. -/

@[expose] public section

namespace Unfoldings.MetricGluing

universe u v

variable {ι : Type u} (E : ι → Type v) [∀ i, PseudoEMetricSpace (E i)]
  {Y : Type*} [PseudoEMetricSpace Y]

/-- A compatible isometric map of each cell into a common space makes every cell map isometric. -/
theorem of_isometry_of_compatible (glue : Total E → Total E → Prop) (f : ∀ i, E i → Y)
    (isometric : ∀ i, Isometry (f i))
    (compatible : ∀ a b, glue a b → f a.1 a.2 = f b.1 b.2) (i : ι) :
    Isometry (of E glue i) := by
  intro x y
  apply le_antisymm (edist_of_le E glue i x y)
  have bound := map_edist_le E glue f (fun i => (isometric i).lipschitzWith) compatible
    ⟨i, x⟩ ⟨i, y⟩
  rw [isometric i x y] at bound
  exact bound

end Unfoldings.MetricGluing
