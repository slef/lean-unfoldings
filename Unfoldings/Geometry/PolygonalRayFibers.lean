module

public import Unfoldings.Geometry.PolygonalRayTransfer
public import Mathlib.Data.Set.Finite.Basic

/-! Bank transport has finite fibers on genuine physical edge and tail parameters. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ}

/-- Forget the parameter while retaining the finite edge or whole-tail tag. -/
def addressPiece : Address n → Option (Fin n)
  | .inl p => some p.1
  | .inr _ => none

/-- A physical polygonal ray may cross itself, but each point has only finitely many
original addresses when every edge and the whole tail are genuine. -/
theorem finite_address_fiber (R : PolygonalRay E n)
    (genuine : ∀ i, R.chain.edge i ≠ 0) (nonzero : R.direction ≠ 0) (x : E) :
    {a : Address n | R.addressPoint a = x}.Finite := by
  apply Set.Finite.of_injOn (f := addressPiece) (t := Set.univ) (fun _ _ => Set.mem_univ _) ?_
    (Set.finite_univ)
  intro a ha b hb pieces
  have same : R.addressPoint a = R.addressPoint b := ha.trans hb.symm
  cases a with
  | inl p =>
    cases b with
    | inl q =>
      have indices : p.1 = q.1 := Option.some.inj pieces
      apply congrArg Sum.inl
      apply Prod.ext indices
      apply Subtype.ext
      change R.chain.point p.1 p.2 = R.chain.point q.1 q.2 at same
      rw [← indices] at same
      exact AffineMap.lineMap_injective ℝ (Ne.symm (sub_ne_zero.mp (genuine p.1))) same
    | inr s => cases (show some p.1 = none from pieces)
  | inr t =>
    cases b with
    | inl q => cases (show none = some q.1 from pieces)
    | inr s =>
      apply congrArg Sum.inr
      apply Subtype.ext
      apply smul_left_injective ℝ nonzero
      exact add_left_cancel same

/-- Transport to a genuine physical bank has finite fibers even if that physical path
crosses itself. No global nonoverlap or physical path injectivity is assumed. -/
theorem finite_mapCarrier_fiber (R : PolygonalRay E n) (outward : R.Outward)
    (genuine : ∀ i, R.chain.edge i ≠ 0) (nonzero : R.direction ≠ 0)
    (Q : PolygonalRay F n) (target_genuine : ∀ i, Q.chain.edge i ≠ 0)
    (target_nonzero : Q.direction ≠ 0) (y : Q.carrier) :
    {x : R.carrier | R.mapCarrier Q x = y}.Finite := by
  apply (finite_address_fiber Q target_genuine target_nonzero y.val).of_surjOn
    (f := fun a => (⟨R.addressPoint a, R.addressPoint_mem a⟩ : R.carrier))
  intro x hx
  obtain ⟨a, equal⟩ := R.exists_address x.property
  have named : (⟨R.addressPoint a, R.addressPoint_mem a⟩ : R.carrier) = x := Subtype.ext equal
  refine ⟨a, ?_, named⟩
  have transported := R.mapCarrier_address outward genuine nonzero Q a
  rw [named] at transported
  exact congrArg Subtype.val (transported.symm.trans hx)

end Unfoldings.PolygonalRay
