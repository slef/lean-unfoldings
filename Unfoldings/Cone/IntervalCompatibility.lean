module

public import Unfoldings.Cone.ConsecutiveCompatibility
public import Unfoldings.Cone.IntervalSeams

/-! All actual radial seams of an interval link respect its angular model. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

theorem tangentCellToAngular_interval_compatible {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (start : C.linkMate retain v chain.first = chain.first)
    (finish : C.linkMate retain v (C.linkTurn retain v chain.last) =
      C.linkTurn retain v chain.last)
    (a b : MetricGluing.Total (C.TangentCell retain v))
    (joined : C.tangentGlue retain v a b) :
    C.tangentCellToAngular retain v chain covers a.1 a.2 =
      C.tangentCellToAngular retain v chain covers b.1 b.2 := by
  obtain ⟨s, x, t, nonnegative, rfl, rfl⟩ := joined
  rcases C.tangentSeam_interval_cases retain v chain covers start finish s with
    ⟨k, source, target⟩ | ⟨k, source, target⟩
  · exact C.tangentCellToAngular_seam_forward retain v chain covers k s x t nonnegative
      source target
  · exact C.tangentCellToAngular_seam_backward retain v chain covers k s x t nonnegative
      source target

end Unfoldings.TriangleComplex
