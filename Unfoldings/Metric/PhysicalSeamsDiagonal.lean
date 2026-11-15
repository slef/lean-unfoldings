module

public import Unfoldings.Metric.PhysicalSeams
public import Unfoldings.Metric.ChangeSeams

/-! Removing same-cell identity seams without changing a physical gluing metric. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing.PhysicalSeams

variable {I X : Type*} [Finite I] [MetricSpace X] {cells : I → Set X} (S : PhysicalSeams cells)

/-- Same-cell attachments identify only identical points, so omit them from seam support. -/
def offDiagonal : PhysicalSeams cells := by
  classical
  exact {
    carrier := fun i j => if i = j then ∅ else S.carrier i j
    closed := fun i j => by split <;> simp_all [S.closed]
    subset_left := fun i j => by split <;> simp_all [S.subset_left]
    subset_right := fun i j => by split <;> simp_all [S.subset_right] }

/-- These are precisely the original seam declarations between different cells. -/
theorem offDiagonal_relation_iff (a b : Total (fun i => cells i)) :
    S.offDiagonal.relation a b ↔ a.1 ≠ b.1 ∧ S.relation a b := by
  classical
  constructor
  · rintro ⟨p, x, rfl, rfl⟩
    have different : p.1 ≠ p.2 := by
      intro equal
      have impossible := x.property
      change x.val ∈ (if p.1 = p.2 then ∅ else S.carrier p.1 p.2) at impossible
      simp only [ite_eq_left equal, Set.mem_empty_iff_false] at impossible
    refine ⟨different, p, ⟨x.val, ?_⟩, rfl, rfl⟩
    have member := x.property
    change x.val ∈ (if p.1 = p.2 then ∅ else S.carrier p.1 p.2) at member
    simpa only [ite_eq_right different] using member
  · rintro ⟨different, p, x, rfl, rfl⟩
    have distinct : p.1 ≠ p.2 := different
    refine ⟨p, ⟨x.val, ?_⟩, rfl, rfl⟩
    change x.val ∈ (if p.1 = p.2 then ∅ else S.carrier p.1 p.2)
    simpa only [ite_eq_right distinct] using x.property

/-- Removing identity seams leaves the actual extended metric unchanged. -/
def offDiagonalIsometryEquiv :
    Realization (fun i => cells i) S.offDiagonal.relation ≃ᵢ
      Realization (fun i => cells i) S.relation :=
  changeSeamsIsometryEquiv (fun i => cells i)
    (fun a b joined => point_eq_of_glue _ ((S.offDiagonal_relation_iff a b).mp joined).2)
    (by
      intro a b joined
      classical
      by_cases different : a.1 ≠ b.1
      · exact point_eq_of_glue _ ((S.offDiagonal_relation_iff a b).mpr ⟨different, joined⟩)
      · have coordinates := S.physical_eq_of_eqvGen (Relation.EqvGen.rel _ _ joined)
        obtain ⟨i, p⟩ := a
        obtain ⟨j, q⟩ := b
        have same : i = j := not_ne_iff.mp different
        subst j
        have identical : p = q := Subtype.ext coordinates
        subst q
        rfl)

@[simp] theorem offDiagonalIsometryEquiv_point (a : Total (fun i => cells i)) :
    S.offDiagonalIsometryEquiv (point (fun i => cells i) S.offDiagonal.relation a) =
      point (fun i => cells i) S.relation a := rfl

end Unfoldings.MetricGluing.PhysicalSeams
