module

public import Unfoldings.Cone.AngularFan
public import Unfoldings.Cone.LinkSeams

/-!
# Angular fans from the constructed vertex-link orders

Every ordered corner contributes its genuine positive Euclidean angle.
The resulting cumulative real headings have total width exactly equal to
the previously defined angle of the retained metric vertex.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

/-- The angular list follows the actual retained-link order. -/
def linkAngularFan {n : ℕ} (chain : (C.linkSystem retain v).Chain n) : AngularFan n where
  angle i := (C.triangle (chain.point i).val.1.1).cornerAngle (chain.point i).val.1.2
  positive _ := (C.triangle _).cornerAngle_pos _
  small _ := (C.triangle _).cornerAngle_lt_pi _

theorem linkAngularFan_totalAngle {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (covers : ∀ p, chain.Visited p) :
    (C.linkAngularFan retain v chain).totalAngle = C.totalAngle retain v := by
  exact C.sum_linkCornerAngle retain v chain covers

theorem linkAngularFan_last_heading {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (covers : ∀ p, chain.Visited p) :
    (C.linkAngularFan retain v chain).heading (Fin.last (n + 1)) = C.totalAngle retain v := by
  rw [AngularFan.heading_last, C.linkAngularFan_totalAngle retain v chain covers]

end Unfoldings.TriangleComplex
