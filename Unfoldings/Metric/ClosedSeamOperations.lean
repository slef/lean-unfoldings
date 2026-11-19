module

public import Unfoldings.Metric.ClosedSeams
public import Unfoldings.Metric.Reparametrize
public import Unfoldings.Metric.IteratedGluing
public import Mathlib.Basic.Finite.Sum

/-! Coordinate changes, finite unions and flattening preserve closed isometric seam data. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing.ClosedSeams

universe u v w z

variable {I : Type u} {E F : I → Type v}
  [∀ i, MetricSpace (E i)] [∀ i, MetricSpace (F i)]

/-- Express the original seams in new cellwise isometric coordinates. -/
def reparametrize (S : ClosedSeams F) (A : ∀ i, E i ≃ᵢ F i) : ClosedSeams E where
  Seam := S.Seam
  Domain := S.Domain
  left := S.left
  right := S.right
  toLeft s := (A (S.left s)).symm ∘ S.toLeft s
  toRight s := (A (S.right s)).symm ∘ S.toRight s
  left_isometry s := (A _).symm.isometry.comp (S.left_isometry s)
  right_isometry s := (A _).symm.isometry.comp (S.right_isometry s)
  left_closed s := by
    rw [Set.range_comp]
    exact (A _).symm.toHomeomorph.isClosedMap _ (S.left_closed s)
  right_closed s := by
    rw [Set.range_comp]
    exact (A _).symm.toHomeomorph.isClosedMap _ (S.right_closed s)

/-- Reparametrization preserves exactly the original oriented relation. -/
theorem reparametrize_relation (S : ClosedSeams F) (A : ∀ i, E i ≃ᵢ F i)
    (x y : Total E) :
    (S.reparametrize A).relation x y ↔ reparametrizeGlue A S.relation x y := by
  constructor
  · rintro ⟨s, p, rfl, rfl⟩
    exact ⟨s, p, congrArg (Sigma.mk (S.left s)) ((A _).apply_symm_apply _),
      congrArg (Sigma.mk (S.right s)) ((A _).apply_symm_apply _)⟩
  · rintro ⟨s, p, first, second⟩
    have undo (a : Total E) (b : Total F)
        (equal : (⟨a.1, A a.1 a.2⟩ : Total F) = b) :
        a = ⟨b.1, (A b.1).symm b.2⟩ := by
      obtain ⟨i, a⟩ := a
      cases equal
      simp
    exact ⟨s, p, undo x _ first, undo y _ second⟩

/-- Keep both finite seam families, with their original domains and orientations. -/
def sum (S T : ClosedSeams E) : ClosedSeams E where
  Seam := S.Seam ⊕ T.Seam
  Domain := Sum.elim S.Domain T.Domain
  metricDomain := fun s => match s with
    | .inl s => S.metricDomain s
    | .inr s => T.metricDomain s
  left := Sum.elim S.left T.left
  right := Sum.elim S.right T.right
  toLeft := fun s => match s with
    | .inl s => S.toLeft s
    | .inr s => T.toLeft s
  toRight := fun s => match s with
    | .inl s => S.toRight s
    | .inr s => T.toRight s
  left_isometry := fun s => match s with
    | .inl s => S.left_isometry s
    | .inr s => T.left_isometry s
  right_isometry := fun s => match s with
    | .inl s => S.right_isometry s
    | .inr s => T.right_isometry s
  left_closed := fun s => match s with
    | .inl s => S.left_closed s
    | .inr s => T.left_closed s
  right_closed := fun s => match s with
    | .inl s => S.right_closed s
    | .inr s => T.right_closed s

/-- Taking a union introduces precisely either of the two declared seams. -/
theorem sum_relation (S T : ClosedSeams E) (x y : Total E) :
    (S.sum T).relation x y ↔ S.relation x y ∨ T.relation x y := by
  constructor
  · rintro ⟨s | s, p, first, second⟩
    · exact Or.inl ⟨s, p, first, second⟩
    · exact Or.inr ⟨s, p, first, second⟩
  · rintro (⟨s, p, first, second⟩ | ⟨s, p, first, second⟩)
    · exact ⟨Sum.inl s, p, first, second⟩
    · exact ⟨Sum.inr s, p, first, second⟩

variable {J : I → Type v} (cells : ∀ i, J i → Type w)
  [Finite I] [∀ i j, MetricSpace (cells i j)]

/-- Place all original internal seam families on the flattened original cell indices. -/
def ofFamily (S : ∀ i, ClosedSeams (cells i)) : ClosedSeams (NestedCell cells) where
  Seam := Σ i, (S i).Seam
  Domain s := (S s.1).Domain s.2
  left s := ⟨s.1, (S s.1).left s.2⟩
  right s := ⟨s.1, (S s.1).right s.2⟩
  toLeft s := (S s.1).toLeft s.2
  toRight s := (S s.1).toRight s.2
  left_isometry s := (S s.1).left_isometry s.2
  right_isometry s := (S s.1).right_isometry s.2
  left_closed s := (S s.1).left_closed s.2
  right_closed s := (S s.1).right_closed s.2

/-- Flattening retains precisely the original internal identifications within each piece. -/
theorem ofFamily_relation (S : ∀ i, ClosedSeams (cells i))
    (a b : Total (NestedCell cells)) :
    (ofFamily cells S).relation a b ↔
      ∃ (i : I) (x y : Total (cells i)), (S i).relation x y ∧
        a = ⟨⟨i, x.1⟩, x.2⟩ ∧ b = ⟨⟨i, y.1⟩, y.2⟩ := by
  constructor
  · rintro ⟨⟨i, s⟩, p, rfl, rfl⟩
    exact ⟨i, ⟨_, _⟩, ⟨_, _⟩, ⟨s, p, rfl, rfl⟩, rfl, rfl⟩
  · rintro ⟨i, x, y, ⟨s, p, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨⟨i, s⟩, p, rfl, rfl⟩

end Unfoldings.MetricGluing.ClosedSeams
