module

public import Unfoldings.Geometry.EdgePerfect

/-! Continuous edge maps are determined by their nonvertex values, including at endpoints. -/

@[expose] public section

namespace Unfoldings.Triangle

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]

theorem edge_eq_of_nonvertex (T : Triangle) (e : Fin 3) (f g : T.Edge e → Y)
    (continuous_f : Continuous f) (continuous_g : Continuous g)
    (agrees : ∀ x : T.Edge e, ¬ T.IsVertex x → f x = g x) : f = g := by
  funext x
  by_contra different
  have open_U : IsOpen {y : T.Edge e | f y ≠ g y} :=
    (isClosed_eq continuous_f continuous_g).isOpen_compl
  obtain ⟨y, unequal, regular⟩ := T.exists_nonvertex_in_edge_neighborhood e x open_U different
  exact unequal (agrees y regular)

end Unfoldings.Triangle
