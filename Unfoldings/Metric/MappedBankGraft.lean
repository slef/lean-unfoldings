module

public import Unfoldings.Metric.BankGraft
public import Unfoldings.Metric.Reparametrize

/-! Intrinsic pieces with concrete cell coordinates retain one exact bank-grafted cell model. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

universe u v w z

variable {I : Type u} {J : I → Type v} {X : I → Type w} [∀ i, EMetricSpace (X i)]
  {B : Type z} {Parameter : B → Type*}
  {Ambient : Type*} [MetricSpace Ambient] (cells : ∀ i, J i → Set Ambient)
  (inner : ∀ i, Total (fun j => cells i j) → Total (fun j => cells i j) → Prop)
  (coordinates : ∀ i, Realization (fun j => cells i j) (inner i) ≃ᵢ X i)
  (left right : ∀ b, Parameter b → Total X)

/-- The original intrinsic point represented by one actual rigid planar-cell point. -/
def mappedNestedPoint (x : Total (NestedCell (fun i j => cells i j))) : Total X :=
  ⟨x.1.1, coordinates x.1.1 (of (fun j => cells x.1.1 j) (inner x.1.1) x.1.2 x.2)⟩

/-- A marked intrinsic point is on cell boundaries if all of its same-piece cell preimages are.
This transports the local condition through dependent piece and cell indices. -/
theorem mappedNestedPoint_boundary {q : Total X}
    (boundary : ∀ j (p : cells q.1 j),
      coordinates q.1 (of (fun j => cells q.1 j) (inner q.1) j p) = q.2 →
        p.val ∉ interior (cells q.1 j))
    (ij : Σ i, J i) (p : cells ij.1 ij.2)
    (named : mappedNestedPoint cells inner coordinates ⟨ij, p⟩ = q) :
    p.val ∉ interior (cells ij.1 ij.2) := by
  subst q
  exact boundary ij.2 p rfl

/-- Internal seams and actual marked-bank attachments use every original cell without padding. -/
abbrev mappedBankGraftCells :=
  NestedGlue (fun i j => cells i j) inner
    (reparametrizeGlue coordinates (bankSeams left right))

/-- The single planar-cell model has exactly the actual intrinsic bank-graft metric. -/
def mappedBankGraftIsometry :
    Realization (NestedCell (fun i j => cells i j))
      (mappedBankGraftCells cells inner coordinates left right) ≃ᵢ BankGraft left right :=
  (nestedIsometryEquiv (fun i j => cells i j) inner
    (reparametrizeGlue coordinates (bankSeams left right))).trans
    (reparametrizeIsometryEquiv coordinates (bankSeams left right))

/-- This exact metric identification preserves the original intrinsic copy of every cell point. -/
theorem mappedBankGraftIsometry_point (ij : Σ i, J i) (p : cells ij.1 ij.2) :
    mappedBankGraftIsometry cells inner coordinates left right
      (of (NestedCell (fun i j => cells i j))
        (mappedBankGraftCells cells inner coordinates left right) ij p) =
      point X (bankSeams left right) (mappedNestedPoint cells inner coordinates ⟨ij, p⟩) := rfl

/-- Every new seam is on actual cell boundaries when its marked bank representatives are.
This criterion depends only on the original piece geometry, not a global development. -/
theorem mappedBankGraftCells_boundary
    (internal : ∀ i j p, p ∈ seamSupport (fun j => cells i j) (inner i) j →
      p.val ∉ interior (cells i j))
    (first_boundary : ∀ b t (ij : Σ i, J i) (p : cells ij.1 ij.2),
      mappedNestedPoint cells inner coordinates ⟨ij, p⟩ = left b t →
        p.val ∉ interior (cells ij.1 ij.2))
    (second_boundary : ∀ b t (ij : Σ i, J i) (p : cells ij.1 ij.2),
      mappedNestedPoint cells inner coordinates ⟨ij, p⟩ = right b t →
        p.val ∉ interior (cells ij.1 ij.2)) :
    ∀ ij p, p ∈ seamSupport (NestedCell (fun i j => cells i j))
      (mappedBankGraftCells cells inner coordinates left right) ij →
        p.val ∉ interior (cells ij.1 ij.2) := by
  have ends (x y : Total (NestedCell (fun i j => cells i j)))
      (related : mappedBankGraftCells cells inner coordinates left right x y) :
      x.2.val ∉ interior (cells x.1.1 x.1.2) ∧
        y.2.val ∉ interior (cells y.1.1 y.1.2) := by
    cases related with
    | inside i a b seam =>
      exact ⟨internal i a.1 a.2 (Or.inl ⟨b, seam⟩),
        internal i b.1 b.2 (Or.inr ⟨a, seam⟩)⟩
    | between a b seam =>
      obtain ⟨bank, t, first, second⟩ := seam
      exact ⟨first_boundary bank t x.1 x.2 first,
        second_boundary bank t y.1 y.2 second⟩
  intro ij p member
  rcases member with ⟨y, seam⟩ | ⟨y, seam⟩
  · exact (ends ⟨ij, p⟩ y seam).1
  · exact (ends y ⟨ij, p⟩ seam).2

end Unfoldings.MetricGluing
