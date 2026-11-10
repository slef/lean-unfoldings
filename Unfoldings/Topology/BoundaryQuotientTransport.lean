module

public import Unfoldings.Topology.BoundaryQuotient

/-! Transport and compose boundary quotients, with explicit control of the collapsed locus. -/

@[expose] public section

noncomputable section

namespace Unfoldings.BoundaryQuotient

variable {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]

def postcomp (Q : BoundaryQuotient A X) (h : X ≃ₜ Y) : BoundaryQuotient A Y where
  projection := ⟨h ∘ Q.projection, h.continuous.comp Q.projection.continuous⟩
  quotient := h.isQuotientMap.comp Q.quotient
  boundary := Q.boundary
  fibers a b equal := Q.fibers a b (h.injective equal)

/-- New target identifications are allowed only above the already marked source boundary. -/
def comp (R : BoundaryQuotient X Y) (Q : BoundaryQuotient A X)
    (absorbed : Q.projection ⁻¹' R.boundary ⊆ Q.boundary) : BoundaryQuotient A Y where
  projection := R.projection.comp Q.projection
  quotient := R.quotient.comp Q.quotient
  boundary := Q.boundary
  fibers a b equal := by
    rcases R.fibers (Q.projection a) (Q.projection b) equal with same | both
    · exact Q.fibers a b same
    · exact Or.inr ⟨absorbed both.1, absorbed both.2⟩

end Unfoldings.BoundaryQuotient
