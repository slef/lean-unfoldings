module

public import Unfoldings.Geometry.BankGapAddressUniqueness

/-! At finite gap vertices only the original adjacent addresses can agree. -/

@[expose] public section

open scoped NNReal

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n) {origin : E}
  (radial : P.RadialFrom origin 0) (genuine : ∀ i, P.edge i ≠ 0)

include radial genuine in
/-- Only edges incident to an original radial-chain vertex can reach it. -/
theorem RadialFrom.point_eq_vertex (i : Fin n) (t : unitInterval) (v : Fin (n + 1))
    (equal : P.point i t = P.vertex v) :
    (i.castSucc = v ∧ t = 0) ∨ (i.succ = v ∧ t = 1) := by
  have monoton := RadialFrom.point_radius_strictMono P radial genuine i
  have vertices := RadialFrom.vertex_radius_strictMono P radial genuine
  have lower := monoton.monotone (show (0 : unitInterval) ≤ t from t.property.1)
  have upper := monoton.monotone (show t ≤ (1 : unitInterval) from t.property.2)
  rw [P.point_zero, equal] at lower
  rw [P.point_one, equal] at upper
  have before := vertices.le_iff_le.mp lower
  have after := vertices.le_iff_le.mp upper
  have endpoint : i.castSucc = v ∨ i.succ = v := by
    change i.val ≤ v.val at before
    change v.val ≤ i.val + 1 at after
    rcases (show v.val = i.val ∨ v.val = i.val + 1 by omega) with start | stop
    · exact Or.inl (Fin.ext start.symm)
    · exact Or.inr (Fin.ext stop.symm)
  rcases endpoint with start | stop
  · refine Or.inl ⟨start, monoton.injective ?_⟩
    rw [P.point_zero, start, equal]
  · refine Or.inr ⟨stop, monoton.injective ?_⟩
    rw [P.point_one, stop, equal]

end Unfoldings.PolygonalChain

namespace Unfoldings.BankGapModel

variable {n : ℕ} {first second : PolygonalRay ℂ (n + 1)}
  (M : BankGapModel first second) (G : OrientedBankGap first second)
  (genuine : ∀ side i, (M.bank side).chain.edge i ≠ 0)

include G genuine in
/-- At a genuine interior bend the only addresses are the adjacent finite edge endpoints,
on the same original bank. In particular the opposite bank and both tails are excluded. -/
theorem addressFrontier_eq_bend (side other : Bool) (k : Fin n)
    (a : PolygonalRay.Address (n + 1))
    (equal : M.addressFrontier other a = M.addressFrontier side (.inl (k.succ, 0))) :
    other = side ∧ (a = .inl (k.castSucc, 1) ∨ a = .inl (k.succ, 0)) := by
  let R := M.bank side
  have outward := M.bank_outward G side
  have vertices := PolygonalChain.RadialFrom.vertex_radius_strictMono R.chain outward.1
    (genuine side)
  have start : (0 : Fin (n + 2)) < k.succ.castSucc := by
    change 0 < k.val + 1
    exact Nat.succ_pos _
  have above := vertices start
  change dist R.start R.start < dist R.start (R.chain.vertex k.succ.castSucc) at above
  have away : R.addressPoint (.inl (k.succ, 0)) ≠ R.start := by
    change R.chain.point k.succ 0 ≠ R.start
    rw [R.chain.point_zero]
    intro same
    rw [same] at above
    exact lt_irrefl _ above
  have same := M.side_eq_of_address_eq G side other (.inl (k.succ, 0)) a away equal.symm
  subst other
  refine ⟨rfl, ?_⟩
  have position : R.addressPoint a = R.chain.point k.succ 0 := congrArg Subtype.val equal
  rw [R.chain.point_zero] at position
  cases a with
  | inl b =>
    rcases b with ⟨i, t⟩
    rcases PolygonalChain.RadialFrom.point_eq_vertex R.chain outward.1 (genuine side)
        i t k.succ.castSucc position with ⟨edge, time⟩ | ⟨edge, time⟩
    · exact Or.inr (congrArg Sum.inl (Prod.ext (Fin.castSucc_injective _ edge) time))
    · rw [← Fin.succ_castSucc] at edge
      exact Or.inl (congrArg Sum.inl (Prod.ext (Fin.succ_injective _ edge) time))
  | inr t =>
    have ordered : k.succ.castSucc < Fin.last (n + 1) := by
      change k.val + 1 < n + 1
      exact Nat.succ_lt_succ k.isLt
    have below := vertices ordered
    have lower := (R.tail_radius_strictMono outward (M.bank_direction_ne_zero G side)).monotone
      (show (0 : ℝ≥0) ≤ t from zero_le)
    change dist R.start (R.tail 0) ≤ dist R.start (R.tail t) at lower
    change R.tail t = R.chain.vertex k.succ.castSucc at position
    rw [R.tail_zero, position] at lower
    exact (not_lt_of_ge lower below).elim

include G genuine in
/-- The common source has exactly the first finite address on each bank and no tail address. -/
theorem address_eq_source (side : Bool) (a : PolygonalRay.Address (n + 1))
    (equal : M.addressFrontier side a = M.addressFrontier false (.inl (0, 0))) :
    a = .inl (0, 0) := by
  let R := M.bank side
  have common : R.start = first.start := by
    cases side
    · rfl
    · exact G.common
  have outward := M.bank_outward G side
  have position : R.addressPoint a = first.chain.point 0 0 := congrArg Subtype.val equal
  rw [first.chain.point_zero, Fin.castSucc_zero] at position
  change R.addressPoint a = first.start at position
  rw [← common] at position
  cases a with
  | inl b =>
    rcases b with ⟨i, t⟩
    obtain ⟨edge, time⟩ := PolygonalChain.RadialFrom.point_eq_first R.chain outward.1
      (genuine side) i t position
    exact congrArg Sum.inl (Prod.ext (Fin.castSucc_injective _ edge) time)
  | inr t =>
    have below := PolygonalChain.RadialFrom.vertex_radius_strictMono R.chain outward.1
      (genuine side) (show (0 : Fin (n + 2)) < Fin.last (n + 1) from Nat.succ_pos n)
    have lower := (R.tail_radius_strictMono outward (M.bank_direction_ne_zero G side)).monotone
      (show (0 : ℝ≥0) ≤ t from zero_le)
    change dist R.start (R.tail 0) ≤ dist R.start (R.tail t) at lower
    change R.tail t = R.start at position
    rw [R.tail_zero, position] at lower
    exact (not_lt_of_ge lower below).elim

end Unfoldings.BankGapModel
