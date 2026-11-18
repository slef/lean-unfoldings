module

public import Unfoldings.Metric.BankStackGraft
public import Unfoldings.Metric.MappedBankGraft

/-! Boundary placement of the actual bank marks derives every stack graft's cell-boundary seams. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

universe u v w

variable {G : Type u} {Edge : Type v} {Parameter : Edge → Type*}
  {J : Option G → Type w} {X : Option G → Type*} [∀ i, EMetricSpace (X i)]
  {Ambient : Type*} [MetricSpace Ambient]
  (cells : ∀ i, J i → Set Ambient)
  (inner : ∀ i, Total (fun j => cells i j) → Total (fun j => cells i j) → Prop)
  (coordinates : ∀ i, Realization (fun j => cells i j) (inner i) ≃ᵢ X i)
  (stack : Edge → List G)
  (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))

/-- No new stack seam meets a cell interior when every original bank mark is on cell boundaries. -/
theorem bankStackCells_boundary
    (internal : ∀ i j p, p ∈ seamSupport (fun j => cells i j) (inner i) j →
      p.val ∉ interior (cells i j))
    (base_boundary : ∀ e side t (ij : Σ i, J i) (p : cells ij.1 ij.2),
      mappedNestedPoint cells inner coordinates ⟨ij, p⟩ = ⟨none, base e side t⟩ →
        p.val ∉ interior (cells ij.1 ij.2))
    (gap_boundary : ∀ e g member side t (ij : Σ i, J i) (p : cells ij.1 ij.2),
      mappedNestedPoint cells inner coordinates ⟨ij, p⟩ = ⟨some g, gap e g member side t⟩ →
        p.val ∉ interior (cells ij.1 ij.2)) :
    ∀ ij p, p ∈ seamSupport (NestedCell (fun i j => cells i j))
      (mappedBankGraftCells cells inner coordinates (bankStackLeft X stack base gap)
        (bankStackRight X stack base gap)) ij → p.val ∉ interior (cells ij.1 ij.2) := by
  apply mappedBankGraftCells_boundary cells inner coordinates _ _ internal
  · intro slot t ij p named
    unfold bankStackLeft at named
    split at named
    · exact base_boundary slot.1 false t ij p named
    · exact gap_boundary slot.1 _ _ true t ij p named
  · intro slot t ij p named
    unfold bankStackRight at named
    split at named
    · exact gap_boundary slot.1 _ _ false t ij p named
    · exact base_boundary slot.1 true t ij p named

end Unfoldings.MetricGluing
