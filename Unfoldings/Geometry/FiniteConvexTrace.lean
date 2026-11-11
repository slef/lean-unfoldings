module

public import Unfoldings.Topology.FiniteIntervalCover
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Order.Compact

/-! Finite closed convex covers give finite labeled whole-piece segment traces. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite ι]

/-- Partition the entire segment into strictly ordered pieces, each in one actual covering cell. -/
theorem exists_finite_closed_convex_segment_partition (cell : ι → Set E)
    (closed : ∀ i, IsClosed (cell i)) (convex : ∀ i, Convex ℝ (cell i)) (p q : E)
    (cover : ∀ x ∈ segment ℝ p q, ∃ i, x ∈ cell i) :
    ∃ n : ℕ, 0 < n ∧ ∃ time : Fin (n + 1) → unitInterval,
      StrictMono time ∧ time 0 = 0 ∧ time (Fin.last n) = 1 ∧
      ∃ piece : Fin n → ι, ∀ i, ∀ t ∈ Set.Icc (time i.castSucc) (time i.succ),
        AffineMap.lineMap p q (t : ℝ) ∈ cell (piece i) := by
  classical
  let := Fintype.ofFinite ι
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap p q
  let times (i : ι) : Set ℝ := Set.Icc 0 1 ∩ line ⁻¹' cell i
  have time_closed (i : ι) : IsClosed (times i) :=
    isClosed_Icc.inter ((closed i).preimage AffineMap.lineMap_continuous)
  have compact (i : ι) : IsCompact (times i) :=
    isCompact_Icc.of_isClosed_subset (time_closed i) (fun _ member => member.1)
  have time_convex (i : ι) : Convex ℝ (times i) :=
    (convex_Icc (0 : ℝ) 1).inter ((convex i).affine_preimage line)
  let Active := {i : ι // (times i).Nonempty}
  have intervals (i : Active) : times i.val = Set.Icc (sInf (times i.val)) (sSup (times i.val)) :=
    eq_Icc_of_connected_compact ⟨i.property, (time_convex i.val).isPreconnected⟩ (compact i.val)
  let lower (i : Active) : unitInterval :=
    ⟨sInf (times i.val), ((compact i.val).sInf_mem i.property).1⟩
  let upper (i : Active) : unitInterval :=
    ⟨sSup (times i.val), ((compact i.val).sSup_mem i.property).1⟩
  have time_cover (t : unitInterval) : ∃ i : Active, lower i ≤ t ∧ t ≤ upper i := by
    obtain ⟨i, member⟩ := cover (line (t : ℝ)) (lineMap_mem_segment ℝ p q t.property)
    have at_t : (t : ℝ) ∈ times i := ⟨t.property, member⟩
    let active : Active := ⟨i, ⟨t, at_t⟩⟩
    exact ⟨active, (Set.ext_iff.mp (intervals active) (t : ℝ)).mp at_t⟩
  obtain ⟨n, _bound, time, increasing, start, finish, piece, contained⟩ :=
    exists_finite_interval_subdivision lower upper time_cover
  have positive : 0 < n := by
    by_contra zero
    have equal : Fin.last n = 0 := Fin.ext (Nat.eq_zero_of_not_pos zero)
    have impossible := finish
    rw [equal, start] at impossible
    exact zero_ne_one impossible
  refine ⟨n, positive, time, increasing, start, finish, fun i => (piece i).val, ?_⟩
  intro i t inside
  have in_interval := contained i inside
  have member : (t : ℝ) ∈ times (piece i).val :=
    (Set.ext_iff.mp (intervals (piece i)) (t : ℝ)).mpr in_interval
  exact member.2

end Unfoldings
