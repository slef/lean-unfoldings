module

public import Unfoldings.Path.Geodesic
public import Unfoldings.Path.FiniteComponent

/-! Distance-realizing bounded-speed paths are geodesics in extended metric spaces. -/

@[expose] public section

open scoped ENNReal

namespace Path

variable {X : Type*} [EMetricSpace X] {a b : X}

/-- Work in a finite-distance component to obtain the usual metric geodesic criterion. -/
theorem isGeodesic_of_eLength_eq_of_lipschitz_emetric (p : Path a b) (finite : p.eLength ≠ ⊤)
    (equal : p.eLength = edist a b) (speed : LipschitzWith p.eLength.toNNReal p) :
    p.IsGeodesic := by
  have start : edist a a ≠ ⊤ := by simp
  let lifted := p.toFiniteComponent start finite
  have length : lifted.eLength = p.eLength := p.eLength_toFiniteComponent start finite
  have speed' : LipschitzWith lifted.eLength.toNNReal lifted := by
    rw [length]
    intro s t
    exact speed s t
  have equal' : lifted.eLength = edist (⟨a, start⟩ : Unfoldings.FiniteComponent a)
      ⟨b, p.finiteComponent_target start finite⟩ := by
    change lifted.eLength = edist a b
    rw [length]
    exact equal
  have geodesic := lifted.isGeodesic_of_eLength_eq_of_lipschitz equal' speed'
  intro s t
  exact geodesic s t

end Path
