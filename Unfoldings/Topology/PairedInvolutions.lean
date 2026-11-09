module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Find
public import Mathlib.Logic.Relation

/-!
# Chains of two involutions

One involution exchanges the two ends of each abstract interval. The other
pairs some interval ends and fixes the remaining boundary ends. Chains visit
each interval once, keeping both endpoint representatives distinct. This
finite combinatorics is independent of triangle geometry and metrics.
-/

@[expose] public section

namespace PairedInvolutions

universe u

/-- Interval ends have a free within-interval involution and a partial endpoint pairing. -/
structure System (X : Type u) where
  turn : X → X
  mate : X → X
  turn_involutive : Function.Involutive turn
  mate_involutive : Function.Involutive mate
  turn_ne : ∀ x, turn x ≠ x

variable {X : Type u} (P : System X)

namespace System

/-- Connectivity uses moves within an interval and across its paired endpoint. -/
def Step (x y : X) : Prop := y = P.turn x ∨ y = P.mate x

def Connected : Prop := ∀ x y, Relation.EqvGen P.Step x y

/-- A nonempty ordered chain of intervals, with no repeated interval in either orientation. -/
structure Chain (n : ℕ) where
  point : Fin (n + 1) → X
  injective : Function.Injective point
  disjoint : ∀ i j, point i ≠ P.turn (point j)
  next : ∀ i : Fin n, P.mate (P.turn (point i.castSucc)) = point i.succ

namespace Chain

variable {P} {n : ℕ} (c : P.Chain n)

def first : X := c.point 0

def last : X := c.point (Fin.last n)

/-- The endpoints represented by the chain, in either orientation. -/
def Visited (x : X) : Prop := ∃ i, x = c.point i ∨ x = P.turn (c.point i)

theorem visited_first : c.Visited c.first := ⟨0, Or.inl rfl⟩

theorem visited_turn {x : X} (inside : c.Visited x) : c.Visited (P.turn x) := by
  obtain ⟨i, rfl | rfl⟩ := inside
  · exact ⟨i, Or.inr rfl⟩
  · exact ⟨i, Or.inl (P.turn_involutive _)⟩

theorem mate_succ (i : Fin n) : P.mate (c.point i.succ) = P.turn (c.point i.castSucc) := by
  rw [← c.next i, P.mate_involutive]

/-- Append the next interval when neither of its endpoints was already visited. -/
def append (q : X) (fresh : ¬ c.Visited q) (joined : P.mate (P.turn c.last) = q) :
    P.Chain (n + 1) where
  point := Fin.snoc c.point q
  injective := Fin.snoc_injective_of_injective c.injective (by
    rintro ⟨i, equal⟩
    exact fresh ⟨i, Or.inl equal.symm⟩)
  disjoint := by
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;>
      refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [Fin.snoc_last] using (P.turn_ne q).symm
    · simpa only [Fin.snoc_last, Fin.snoc_castSucc] using
        (fun h => fresh ⟨j, Or.inr h⟩)
    · simp only [Fin.snoc_last, Fin.snoc_castSucc]
      intro equal
      have opposite : q = P.turn (c.point i) := by
        rw [equal, P.turn_involutive]
      exact fresh ⟨i, Or.inr opposite⟩
    · simpa only [Fin.snoc_castSucc] using c.disjoint i j
  next := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, last] using joined
    · rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
      exact c.next j

@[simp] theorem append_first (q : X) (fresh : ¬ c.Visited q)
    (joined : P.mate (P.turn c.last) = q) : (c.append q fresh joined).first = c.first := by
  change Fin.snoc (α := fun _ : Fin (n + 2) => X) c.point q
    (0 : Fin (n + 1)).castSucc = c.point 0
  rw [Fin.snoc_castSucc]

include c in
theorem length_le_card [Fintype X] : n + 1 ≤ Fintype.card X := by
  simpa using Fintype.card_le_of_injective c.point c.injective

/-- A first collision closes the chain or reaches an unpaired terminal endpoint. -/
theorem closes_or_boundary (inside : c.Visited (P.mate (P.turn c.last))) :
    P.mate (P.turn c.last) = c.first ∨ P.mate (P.turn c.last) = P.turn c.last := by
  obtain ⟨i, point | opposite⟩ := inside
  · revert point
    refine Fin.cases ?_ (fun j => ?_) i
    · intro point
      exact Or.inl point
    · intro point
      have previous := congrArg P.mate point
      rw [P.mate_involutive, c.mate_succ j] at previous
      have index := c.injective (P.turn_involutive.injective previous)
      have values := congrArg Fin.val index
      have bound := j.isLt
      simp only [Fin.val_last, Fin.val_castSucc] at values
      omega
  · revert opposite
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro opposite
      exact Or.inr opposite
    · intro opposite
      have collision := congrArg P.mate opposite
      rw [P.mate_involutive, c.next j] at collision
      exact (c.disjoint j.succ (Fin.last n) collision.symm).elim

/-- A chain closed at both ends is invariant under endpoint pairing. -/
theorem visited_mate
    (start : P.mate c.first = P.turn c.last ∨ P.mate c.first = c.first)
    (finish : P.mate (P.turn c.last) = c.first ∨ P.mate (P.turn c.last) = P.turn c.last)
    {x : X} (inside : c.Visited x) : c.Visited (P.mate x) := by
  obtain ⟨i, rfl | rfl⟩ := inside
  · refine Fin.cases ?_ (fun j => ?_) i
    · rcases start with start | start
      · exact ⟨Fin.last n, Or.inr start⟩
      · exact ⟨0, Or.inl start⟩
    · exact ⟨j.castSucc, Or.inr (c.mate_succ j)⟩
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · rcases finish with finish | finish
      · exact ⟨0, Or.inl finish⟩
      · exact ⟨Fin.last n, Or.inr finish⟩
    · exact ⟨j.succ, Or.inl (c.next j)⟩

/-- In a connected system a chain closed at both ends visits every endpoint. -/
theorem covers (connected : P.Connected)
    (start : P.mate c.first = P.turn c.last ∨ P.mate c.first = c.first)
    (finish : P.mate (P.turn c.last) = c.first ∨ P.mate (P.turn c.last) = P.turn c.last) :
    ∀ x, c.Visited x := by
  have invariant {x y : X} (related : Relation.EqvGen P.Step x y) : c.Visited x ↔ c.Visited y := by
    induction related with
    | rel x y h =>
      rcases h with rfl | rfl
      · exact ⟨c.visited_turn, fun h => by
          exact (P.turn_involutive x) ▸ c.visited_turn h⟩
      · exact ⟨c.visited_mate start finish, fun h => by
          exact (P.mate_involutive x) ▸ c.visited_mate start finish h⟩
    | refl x => rfl
    | symm x y h ih => exact ih.symm
    | trans x y z hxy hyz ih₁ ih₂ => exact ih₁.trans ih₂
  intro x
  exact (invariant (connected c.first x)).mp c.visited_first

/-- An interval chain has exactly its two outer endpoints unpaired. -/
theorem mate_fixed_iff (start : P.mate c.first = c.first)
    (finish : P.mate (P.turn c.last) = P.turn c.last) (covers : ∀ x, c.Visited x) (x : X) :
    P.mate x = x ↔ x = c.first ∨ x = P.turn c.last := by
  constructor
  · intro fixed
    obtain ⟨i, point | opposite⟩ := covers x
    · subst x
      revert fixed
      refine Fin.cases ?_ (fun j => ?_) i
      · intro _
        exact Or.inl rfl
      · intro fixed
        exact (c.disjoint j.succ j.castSucc (fixed.symm.trans (c.mate_succ j))).elim
    · subst x
      revert fixed
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro _
        exact Or.inr rfl
      · intro fixed
        exact (c.disjoint j.succ j.castSucc ((c.next j).symm.trans fixed)).elim
  · rintro (rfl | rfl)
    · exact start
    · exact finish

/-- Enumerate both endpoints of every interval in the chain. -/
def flag (p : Fin (n + 1) × Bool) : X :=
  if p.2 then P.turn (c.point p.1) else c.point p.1

theorem flag_injective : Function.Injective c.flag := by
  rintro ⟨i, b⟩ ⟨j, d⟩ equal
  cases b <;> cases d
  · exact Prod.ext (c.injective equal) rfl
  · exact (c.disjoint i j equal).elim
  · exact (c.disjoint j i equal.symm).elim
  · exact Prod.ext (c.injective (P.turn_involutive.injective equal)) rfl

theorem flag_surjective (covers : ∀ x, c.Visited x) : Function.Surjective c.flag := by
  intro x
  obtain ⟨i, point | opposite⟩ := covers x
  · exact ⟨(i, false), point.symm⟩
  · exact ⟨(i, true), opposite.symm⟩

/-- A spanning chain gives a complete endpoint enumeration, including the one-interval cycle. -/
noncomputable def flagEquiv (covers : ∀ x, c.Visited x) : Fin (n + 1) × Bool ≃ X :=
  Equiv.ofBijective c.flag ⟨c.flag_injective, c.flag_surjective covers⟩

end Chain

/-- A chain consisting of one interval and its two distinct endpoints. -/
def singleton (x : X) : P.Chain 0 where
  point := fun _ => x
  injective := by intro i j _; apply Fin.ext; omega
  disjoint := fun _ _ => (P.turn_ne x).symm
  next := Fin.elim0

/-- A maximal chain has its next endpoint already among its represented endpoints. -/
theorem exists_closed_chain [Finite X] (x : X) : ∃ n, ∃ c : P.Chain n,
    c.first = x ∧ c.Visited (P.mate (P.turn c.last)) := by
  classical
  let _ := Fintype.ofFinite X
  let exists_chain (n : ℕ) := ∃ c : P.Chain n, c.first = x
  let N := Nat.findGreatest exists_chain (Fintype.card X)
  have initial : exists_chain 0 := ⟨P.singleton x, rfl⟩
  obtain ⟨c, first⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card X)) initial
  refine ⟨N, c, first, ?_⟩
  by_contra fresh
  let q := P.mate (P.turn c.last)
  let extended := c.append q fresh rfl
  have bounded : N + 1 ≤ Fintype.card X := by
    have bound := extended.length_le_card
    omega
  have larger : exists_chain (N + 1) := ⟨extended, (c.append_first q fresh rfl).trans first⟩
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self N) bounded larger

/-- A connected system with no unpaired ends has a cyclic interval ordering. -/
theorem exists_cycle_chain [Finite X] (connected : P.Connected)
    (no_boundary : ∀ x, P.mate x ≠ x) (x : X) : ∃ n, ∃ c : P.Chain n,
    c.first = x ∧ P.mate (P.turn c.last) = c.first ∧ ∀ y, c.Visited y := by
  obtain ⟨n, c, first, inside⟩ := P.exists_closed_chain x
  rcases c.closes_or_boundary inside with closes | boundary
  · have start : P.mate c.first = P.turn c.last := by
      rw [← closes, P.mate_involutive]
    exact ⟨n, c, first, closes, c.covers connected (Or.inl start) (Or.inl closes)⟩
  · exact (no_boundary _ boundary).elim

/-- Starting at an unpaired end gives an interval ordering ending at another unpaired end. -/
theorem exists_interval_chain [Finite X] (connected : P.Connected) (x : X)
    (boundary : P.mate x = x) : ∃ n, ∃ c : P.Chain n,
    c.first = x ∧ P.mate (P.turn c.last) = P.turn c.last ∧ ∀ y, c.Visited y := by
  obtain ⟨n, c, first, inside⟩ := P.exists_closed_chain x
  have start : P.mate c.first = c.first := by rw [first, boundary]
  have finish : P.mate (P.turn c.last) = P.turn c.last := by
    rcases c.closes_or_boundary inside with closes | finish
    · have opposite : P.turn c.last = c.first := by
        have mapped := congrArg P.mate closes
        rwa [P.mate_involutive, start] at mapped
      exact (c.disjoint 0 (Fin.last n) opposite.symm).elim
    · exact finish
  exact ⟨n, c, first, finish, c.covers connected (Or.inr start) (Or.inr finish)⟩

end System
end PairedInvolutions
