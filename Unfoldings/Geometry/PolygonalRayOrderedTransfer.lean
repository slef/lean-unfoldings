module

public import Unfoldings.Geometry.PolygonalRayTransfer
public import Unfoldings.Geometry.BankRadialOrder

/-! A strictly ascending physical ray retains all original bank parameters. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ}

private theorem transfer_finite_of_ordered (Q : PolygonalRay E n) (B : PolygonalRay F n)
    (value : E → ℝ) (edges : ∀ i, StrictMono (value ∘ Q.chain.point i))
    (vertices : StrictMono (value ∘ Q.chain.vertex))
    (i j : Fin n) (t u : unitInterval) (before : PolygonalChain.Before i t j u)
    (same : value (Q.chain.point i t) = value (Q.chain.point j u)) :
    B.chain.point i t = B.chain.point j u := by
  rcases before with earlier | ⟨rfl, _⟩
  · have first : value (Q.chain.point i t) ≤ value (Q.chain.vertex i.succ) := by
      rw [← Q.chain.point_one]
      exact (edges i).monotone t.property.2
    have mid : value (Q.chain.vertex i.succ) ≤ value (Q.chain.vertex j.castSucc) :=
      vertices.monotone (by change i.val + 1 ≤ j.val; exact earlier)
    have last : value (Q.chain.vertex j.castSucc) ≤ value (Q.chain.point j u) := by
      rw [← Q.chain.point_zero]
      exact (edges j).monotone u.property.1
    have at_joint : i.succ = j.castSucc := vertices.injective
      (le_antisymm mid (last.trans (same.symm.trans_le first)))
    have at_one : t = 1 := (edges i).injective (by
      change value (Q.chain.point i t) = value (Q.chain.point i 1)
      rw [Q.chain.point_one]
      exact le_antisymm first (mid.trans (last.trans_eq same.symm)))
    have at_zero : u = 0 := (edges j).injective (by
      change value (Q.chain.point j u) = value (Q.chain.point j 0)
      rw [Q.chain.point_zero]
      exact le_antisymm (same.symm.trans_le (first.trans mid)) last)
    rw [at_one, at_zero, B.chain.point_one, B.chain.point_zero, at_joint]
  · rw [(edges i).injective same]

/-- A strictly increasing scalar along the physical ray makes all original edge
addresses transport faithfully when the true tail leaves the finite path. -/
theorem transfer_address_eq_of_ordered (Q : PolygonalRay E n) (B : PolygonalRay F n)
    (value : E → ℝ) (edges : ∀ i, StrictMono (value ∘ Q.chain.point i))
    (nonzero : Q.direction ≠ 0)
    (outside : ∀ i t s, 0 < s → Q.tail s ≠ Q.chain.point i t) (a b : Address n)
    (same : Q.addressPoint a = Q.addressPoint b) :
    B.addressPoint a = B.addressPoint b := by
  have vertices : StrictMono (value ∘ Q.chain.vertex) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    have step : value (Q.chain.point i 0) < value (Q.chain.point i 1) := edges i zero_lt_one
    rw [Q.chain.point_zero, Q.chain.point_one] at step
    exact step
  have mixed (i : Fin n) (s : unitInterval) (t : ℝ≥0)
      (equal : Q.chain.point i s = Q.tail t) : B.chain.point i s = B.tail t := by
    have first : value (Q.chain.point i s) ≤ value (Q.chain.vertex i.succ) := by
      rw [← Q.chain.point_one]
      exact (edges i).monotone s.property.2
    have middle : value (Q.chain.vertex i.succ) ≤ value (Q.chain.vertex (Fin.last n)) :=
      vertices.monotone (Fin.le_last _)
    have t_zero : t = 0 := by
      by_contra different
      exact outside i s t (pos_iff_ne_zero.mpr different) equal.symm
    rw [t_zero, Q.tail_zero] at equal
    have same_value := congrArg value equal
    have at_end : i.succ = Fin.last n :=
      vertices.injective (le_antisymm middle (same_value.symm.trans_le first))
    have s_one : s = 1 := (edges i).injective (by
      change value (Q.chain.point i s) = value (Q.chain.point i 1)
      rw [Q.chain.point_one, at_end]
      exact same_value)
    rw [s_one, B.chain.point_one, at_end, t_zero, B.tail_zero]
  cases a with
  | inl p =>
    cases b with
    | inl q =>
      have eq : value (Q.chain.point p.1 p.2) = value (Q.chain.point q.1 q.2) := congrArg value same
      rcases PolygonalChain.before_total p.1 q.1 p.2 q.2 with before | after
      · exact transfer_finite_of_ordered Q B value edges vertices _ _ _ _ before eq
      · exact (transfer_finite_of_ordered Q B value edges vertices _ _ _ _ after eq.symm).symm
    | inr t => exact mixed _ _ _ same
  | inr t =>
    cases b with
    | inl q => exact (mixed _ _ _ same.symm).symm
    | inr u =>
      have vectors : t.val • Q.direction = u.val • Q.direction := add_left_cancel same
      have vanish : (t.val - u.val) • Q.direction = 0 := by
        rw [sub_smul, vectors, sub_self]
      have different := (smul_eq_zero.mp vanish).resolve_right nonzero
      exact congrArg B.tail (Subtype.ext (sub_eq_zero.mp different))

/-- Transferring a radial parameter to a strictly ascending physical bank is injective. -/
theorem mapCarrier_injective_of_ordered (B : PolygonalRay F n) (outward : B.Outward)
    (genuine : ∀ i, B.chain.edge i ≠ 0) (nonzero : B.direction ≠ 0)
    (Q : PolygonalRay E n) (value : E → ℝ)
    (edges : ∀ i, StrictMono (value ∘ Q.chain.point i)) (target : Q.direction ≠ 0)
    (outside : ∀ i t s, 0 < s → Q.tail s ≠ Q.chain.point i t) :
    Function.Injective (B.mapCarrier Q) := by
  intro x y same
  obtain ⟨a, ax⟩ := B.exists_address x.property
  obtain ⟨b, by'⟩ := B.exists_address y.property
  have x_eq : (⟨B.addressPoint a, B.addressPoint_mem a⟩ : B.carrier) = x := Subtype.ext ax
  have y_eq : (⟨B.addressPoint b, B.addressPoint_mem b⟩ : B.carrier) = y := Subtype.ext by'
  have ha := B.mapCarrier_address outward genuine nonzero Q a
  have hb := B.mapCarrier_address outward genuine nonzero Q b
  rw [x_eq] at ha
  rw [y_eq] at hb
  have named := congrArg Subtype.val (ha.symm.trans (same.trans hb))
  have address := Q.transfer_address_eq_of_ordered B value edges target outside a b named
  exact Subtype.ext (ax.symm.trans (address.trans by'))

end Unfoldings.PolygonalRay
