module

public import Mathlib.Data.Fintype.Sort
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Prod.Lex.Basic

/-! Enumerate an arbitrary finite type by a real height, allowing ties. -/

@[expose] public section

namespace Unfoldings

theorem exists_height_ordered_equiv {α : Type*} [Finite α] (height : α → ℝ) :
    ∃ (n : ℕ) (e : Fin n ≃ α), Monotone (height ∘ e) := by
  classical
  let := Fintype.ofFinite α
  let index := Fintype.equivFin α
  let key : α → ℝ ×ₗ Fin (Fintype.card α) := fun a => toLex (height a, index a)
  have injective : Function.Injective key := by
    intro a b equal
    exact index.injective (congrArg (fun x => (ofLex x).2) equal)
  let := LinearOrder.lift' key injective
  let e := monoEquivOfFin α rfl
  refine ⟨Fintype.card α, e.toEquiv, ?_⟩
  intro a b ordered
  exact Prod.Lex.monotone_fst (key (e a)) (key (e b)) (e.monotone ordered)

end Unfoldings
