module

public import Unfoldings.Complex.BoundaryCycleEnumeration

/-! A complete cyclic order of the actual bank boundary, independent of its planar image. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face) (retain : Set C.Seam)

structure BoundaryContour where
  length : ℕ
  cycle : (C.boundarySystem retain).Chain length
  closes : C.boundaryMate retain (C.boundaryTurn retain cycle.last) = cycle.first
  covers : ∀ p, cycle.Visited p

def boundaryContourOfConnected
    (connected : (C.boundaryGraph retain).adjacencyGraph.Connected) : C.BoundaryContour retain := by
  exact Classical.choice (by
    obtain ⟨n, cycle, closes, covers⟩ := C.exists_boundaryCycle_cover_of_connected retain connected
    exact ⟨⟨n, cycle, closes, covers⟩⟩)

end Unfoldings.TriangleComplex
