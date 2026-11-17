module

public import Unfoldings.Roof.CompatiblePotentialPaths
public import Unfoldings.Geometry.ChainAppend

/-! Append any finite terminal-ray continuation while retaining the original compatible routing. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

/-- An exact original terminal endpoint permits arbitrarily long finite continuations.
There is no upper truncation on the appended terminal time. -/
theorem follows_snoc_terminal {n : ℕ} (P : PolygonalChain Plane n) (follows : R.Follows P)
    (r : {v // v ∈ R.parents.roots}) {s t : ℝ} (nonnegative : 0 ≤ s) (ordered : s ≤ t)
    (endpoint : P.vertex (Fin.last n) = R.exterior.ray (R.terminalIndex r) s) :
    R.Follows (P.snoc (R.exterior.ray (R.terminalIndex r) t)) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change R.FollowsStep
      ((P.snoc _).vertex (Fin.last n).castSucc) ((P.snoc _).vertex (Fin.last (n + 1)))
    rw [P.snoc_vertex_castSucc, P.snoc_vertex_last, endpoint]
    exact Or.inr ⟨r, s, t, nonnegative, ordered, rfl, rfl⟩
  · change R.FollowsStep
      ((P.snoc _).vertex j.castSucc.castSucc) ((P.snoc _).vertex j.succ.castSucc)
    rw [P.snoc_vertex_castSucc, P.snoc_vertex_castSucc]
    exact follows j

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
