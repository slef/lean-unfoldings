module

public import Unfoldings.Basic
public import Schoenflies.Concatenate
public import Mathlib.Topology.Path

/-! Injective unit-interval paths provide actual named-endpoint arcs for Jordan constructions. -/

@[expose] public section

namespace Unfoldings.PlanarTopology

/-- Convert an actual injective path, retaining its exact range and endpoints. -/
theorem isArcBetween_of_injective_path {a b : Plane} (P : Path a b)
    (injective : Function.Injective P) : Schoenflies.IsArcBetween (Set.range P) a b := by
  refine ⟨P.extend, P.extend.continuous.continuousOn, ?_, P.image_extend_of_subset Set.Subset.rfl,
    P.extend_zero, P.extend_one⟩
  intro s hs t ht equal
  rw [P.extend_apply hs, P.extend_apply ht] at equal
  exact congrArg Subtype.val (injective equal)

end Unfoldings.PlanarTopology
