module

public import Unfoldings.Metric.IteratedGluing
public import Unfoldings.Metric.Local

/-! Actual marked-bank grafts retain their piece metrics and a single underlying cell model. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

universe u v w z

variable {I : Type u} {B : Type v} {A : B → Type w} {X : I → Type z}
  [∀ i, PseudoEMetricSpace (X i)]
  (left right : ∀ b, A b → Total X)

/-- Identify the two named intrinsic bank points at every original bank parameter. -/
def bankSeams (x y : Total X) : Prop := ∃ b t, x = left b t ∧ y = right b t

/-- The metric graft is the genuine route metric of the original pieces and marked bank seams. -/
abbrev BankGraft := Realization X (bankSeams left right)

/-- Every original metric piece maps nonexpansively into the assembled graft. -/
theorem bankGraft_piece_lipschitz (i : I) :
    LipschitzWith 1 (of X (bankSeams left right) i) := of_lipschitz X _ i

/-- Both marked banks have identical images at each original parameter, including endpoints. -/
theorem bankGraft_banks_equal (b : B) (t : A b) :
    point X (bankSeams left right) (left b t) =
      point X (bankSeams left right) (right b t) :=
  point_eq_of_glue X ⟨b, t, rfl, rfl⟩

section Cells

variable {J : I → Type*} {Ambient : Type*} [MetricSpace Ambient]
  (cells : ∀ i, J i → Set Ambient)
  (inner : ∀ i, Total (fun j => cells i j) → Total (fun j => cells i j) → Prop)
  (first second : ∀ b : B, A b → Total (fun i => Realization (fun j => cells i j) (inner i)))

/-- A graft keeps every original cell and both levels of bank identifications. -/
abbrev bankGraftCells :=
  NestedGlue (fun i j => cells i j) inner (bankSeams first second)

/-- Gluing whole intrinsic pieces and gluing all their original cells give exactly the same
metric space, even for unbounded pieces. No development or nonoverlap is input. -/
def bankGraftCellIsometryEquiv :
    Realization (NestedCell (fun i j => cells i j)) (bankGraftCells cells inner first second) ≃ᵢ
      BankGraft first second :=
  nestedIsometryEquiv (fun i j => cells i j) inner (bankSeams first second)

/-- Every original cell point keeps its literal metric copy under the gluing equivalence. -/
theorem bankGraftCellIsometryEquiv_point (i : I) (j : J i) (x : cells i j) :
    bankGraftCellIsometryEquiv cells inner first second
      (of (NestedCell (fun i j => cells i j)) (bankGraftCells cells inner first second) ⟨i, j⟩ x) =
      of (fun i => Realization (fun j => cells i j) (inner i)) (bankSeams first second) i
        (of (fun j => cells i j) (inner i) j x) := rfl

/-- Local bank-boundary placement and original boundary-only seams derive boundary-only gluing
for the complete graft's underlying cells. There is no assumed global separation property. -/
theorem bankGraftCells_boundary
    (internal : ∀ i j x, x ∈ seamSupport (fun j => cells i j) (inner i) j →
      x.val ∉ interior (cells i j))
    (first_boundary : ∀ b t ij (x : cells ij.1 ij.2),
      nestedPoint (fun i j => cells i j) inner ⟨ij, x⟩ = first b t →
        x.val ∉ interior (cells ij.1 ij.2))
    (second_boundary : ∀ b t ij (x : cells ij.1 ij.2),
      nestedPoint (fun i j => cells i j) inner ⟨ij, x⟩ = second b t →
        x.val ∉ interior (cells ij.1 ij.2)) :
    ∀ ij x, x ∈ seamSupport (NestedCell (fun i j => cells i j))
      (bankGraftCells cells inner first second) ij → x.val ∉ interior (cells ij.1 ij.2) := by
  have ends (x y : Total (NestedCell (fun i j => cells i j)))
      (related : bankGraftCells cells inner first second x y) :
      x.2.val ∉ interior (cells x.1.1 x.1.2) ∧
        y.2.val ∉ interior (cells y.1.1 y.1.2) := by
    cases related with
    | inside i a b seam =>
      exact ⟨internal i a.1 a.2 (Or.inl ⟨b, seam⟩),
        internal i b.1 b.2 (Or.inr ⟨a, seam⟩)⟩
    | between a b seam =>
      obtain ⟨bank, t, first_name, second_name⟩ := seam
      exact ⟨first_boundary bank t x.1 x.2 first_name,
        second_boundary bank t y.1 y.2 second_name⟩
  intro ij x member
  rcases member with ⟨y, seam⟩ | ⟨y, seam⟩
  · exact (ends ⟨ij, x⟩ y seam).1
  · exact (ends y ⟨ij, x⟩ seam).2

end Cells

end Unfoldings.MetricGluing
