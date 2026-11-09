module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Bounded relation paths inside exact fibers

A relation preserving a map generates a graph on each fiber. Equivalence
chains give graph reachability there. Removing loops in a finite fiber gives
a simple path shorter than its cardinality. This isolates a combinatorial
ingredient needed to normalize face routes at seam and vertex crossings.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {A X : Type*} (f : A → X) (r : A → A → Prop)

def fiberGraph (x : X) : SimpleGraph {a : A // f a = x} :=
  SimpleGraph.fromRel (fun a b => r a.val b.val)

theorem fiberGraph_reachable (compatible : ∀ a b, r a b → f a = f b)
    {x : X} {a b : A} (related : Relation.EqvGen r a b) :
    ∀ ha : f a = x, ∀ hb : f b = x,
      (fiberGraph f r x).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  have preserves {a b : A} (h : Relation.EqvGen r a b) : f a = f b := by
    induction h with
    | rel a b h => exact compatible a b h
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ first last => exact first.trans last
  induction related with
  | rel a b h =>
    intro ha hb
    by_cases equal : a = b
    · subst b
      exact SimpleGraph.Reachable.refl _
    · apply SimpleGraph.Adj.reachable
      exact ⟨fun same => equal (congrArg Subtype.val same), Or.inl h⟩
  | refl a =>
    intro ha hb
    exact SimpleGraph.Reachable.refl _
  | symm a b _ ih =>
    intro hb ha
    exact (ih ha hb).symm
  | trans a b c first _ ih_first ih_last =>
    intro ha hc
    have hb : f b = x := (preserves first).symm.trans ha
    exact (ih_first ha hb).trans (ih_last hb hc)

theorem fiberGraph_exists_short_path (compatible : ∀ a b, r a b → f a = f b)
    {x : X} [Fintype {a : A // f a = x}] (a b : {a : A // f a = x})
    (related : Relation.EqvGen r a.val b.val) :
    ∃ p : (fiberGraph f r x).Path a b,
      p.val.length < Fintype.card {a : A // f a = x} := by
  classical
  have reachable := fiberGraph_reachable f r compatible related a.property b.property
  let p := (Classical.choice reachable).toPath
  exact ⟨p, p.property.length_lt⟩

end Unfoldings
