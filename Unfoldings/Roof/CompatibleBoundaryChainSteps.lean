module

public import Unfoldings.Roof.CompatiblePotentialPaths
public import Unfoldings.Polyhedron.ProjectedBoundaryChain
public import Unfoldings.Topology.ChainConcatRange

/-! Actual boundary-chain assembly preserves compatible physical routing at every bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v w z

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)
  {Fine : Type w} [Fintype Fine] {D : TriangleComplex.{w, z} Fine} (F : SpatialFolding D)
  {retain : Set D.Seam}

/-- Actual polygon vertices use exactly their directed cut-bank endpoints. -/
theorem follows_projectedBoundaryChain_iff {n : ℕ}
    (chain : (D.boundarySystem retain).Chain n) :
    R.Follows (F.projectedBoundaryChain chain) ↔ ∀ i,
      R.FollowsStep (Cap.horizontal (F.boundaryPosition (chain.point i)))
        (Cap.horizontal (F.boundaryPosition (D.boundaryTurn retain (chain.point i)))) := by
  constructor
  · intro follows i
    exact Eq.mp (congrArg₂ R.FollowsStep
      (F.projectedBoundaryChain_vertex_castSucc chain i)
      (F.projectedBoundaryChain_vertex_succ chain i)) (follows i)
  · intro follows i
    exact Eq.mpr (congrArg₂ R.FollowsStep
      (F.projectedBoundaryChain_vertex_castSucc chain i)
      (F.projectedBoundaryChain_vertex_succ chain i)) (follows i)

/-- Joining actual matching bank chains keeps every original compatible routing step. -/
theorem follows_projectedBoundaryChain_concat {n m : ℕ}
    (first : (D.boundarySystem retain).Chain n) (last : (D.boundarySystem retain).Chain m)
    (separated : ∀ i j, first.point i ≠ last.point j ∧
      first.point i ≠ D.boundaryTurn retain (last.point j))
    (joined : D.boundaryMate retain (D.boundaryTurn retain first.last) = last.first)
    (follows_first : R.Follows (F.projectedBoundaryChain first))
    (follows_last : R.Follows (F.projectedBoundaryChain last)) :
    R.Follows (F.projectedBoundaryChain (first.concat last separated joined)) := by
  let full := first.concat last separated joined
  let test (p : D.BoundaryEnd retain) := R.FollowsStep
    (Cap.horizontal (F.boundaryPosition p))
    (Cap.horizontal (F.boundaryPosition (D.boundaryTurn retain p)))
  apply (R.follows_projectedBoundaryChain_iff F full).mpr
  intro j
  rcases (first.concat_point_range_iff last separated joined (full.point j)).mp ⟨j, rfl⟩ with
    ⟨k, named⟩ | ⟨k, named⟩
  · exact Eq.mp (congrArg test named)
      ((R.follows_projectedBoundaryChain_iff F first).mp follows_first k)
  · exact Eq.mp (congrArg test named)
      ((R.follows_projectedBoundaryChain_iff F last).mp follows_last k)

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
