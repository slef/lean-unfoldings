module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Common coordinate spaces. Distances on these spaces are ambient Euclidean
distances; intrinsic and cut metrics are constructed on separate types. -/

@[expose] public section

namespace Unfoldings

/-- Local coordinates for a Euclidean face and its planar development. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Coordinates for an optional embedded polyhedral surface. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

end Unfoldings
