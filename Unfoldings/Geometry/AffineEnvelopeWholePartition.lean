module

public import Unfoldings.Geometry.AffineEnvelope
public import Unfoldings.Geometry.ChamberTriangulation
public import Unfoldings.Geometry.UnboundedArrangement

/-! Finite unbounded active-plane partitions respecting arbitrary prescribed affine lines. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AffineEnvelope

universe u

variable {I J : Type u} [Fintype I] [Nonempty I] [Finite J]
  (support : I → Plane →ᵃ[ℝ] ℝ) (extra : J → Plane →ᵃ[ℝ] ℝ)

/-- All nontrivial support-plane intersections and all prescribed extra lines. -/
def wholePartitionEquation :
    {p : I × I // support p.1 ≠ support p.2} ⊕ J → Plane →ᵃ[ℝ] ℝ :=
  Sum.elim (fun p => support p.val.1 - support p.val.2) extra

/-- Construct full-dimensional closed convex cells covering the whole plane, on
which the actual envelope is one chosen support. No outer truncation is introduced. -/
theorem exists_whole_constrained_cell_partition (proper_extra : ∀ j, extra j ≠ 0) :
    ∃ (A : Type u) (_ : Fintype A) (cells : A → Set Plane) (plane : A → I)
      (signs : A → J → Bool),
      (∀ a, IsClosed (cells a) ∧ Convex ℝ (cells a) ∧ (interior (cells a)).Nonempty) ∧
      (∀ a b, a ≠ b → Disjoint (interior (cells a)) (interior (cells b))) ∧
      (⋃ a, cells a) = Set.univ ∧
      (∀ a p, p ∈ cells a → height support p = support (plane a) p) ∧
      (∀ a p, p ∈ cells a → ∀ j, 0 ≤ AffineArrangement.signed (extra j) (signs a j) p) := by
  classical
  let equation := wholePartitionEquation support extra
  have proper : ∀ i, equation i ≠ 0 := by
    intro i
    cases i with
    | inl pair => exact fun zero => pair.property (sub_eq_zero.mp zero)
    | inr j => exact proper_extra j
  obtain ⟨S, finite, nonempty, cover⟩ :=
    AffineArrangement.exists_finite_unbounded_chamber_cover equation proper isClosed_univ
      (by simp) (by simp)
  let : Fintype S := finite.fintype
  let cells (a : S) := AffineArrangement.closedChamber equation a.val
  have active (a : S) : ∃ i, ∀ p ∈ cells a, height support p = support i p := by
    obtain ⟨p, inside⟩ := (nonempty a.val a.property).1
    obtain ⟨i, realizes⟩ := exists_height_eq support p
    refine ⟨i, fun x hx => (mem_cell_iff support i x).mp (fun j => ?_)⟩
    by_cases same : support j = support i
    · exact (congrArg (fun h : Plane →ᵃ[ℝ] ℝ => h x) same).symm.le
    · have order := height_le support p j
      rw [realizes] at order
      have sign := AffineArrangement.closedChamber_nonnegative_of_chamber_nonnegative equation
        a.val inside hx (.inl ⟨(j, i), same⟩)
        (show 0 ≤ equation (.inl ⟨(j, i), same⟩) p from sub_nonneg.mpr order)
      exact sub_nonneg.mp sign
  choose plane on_plane using active
  refine ⟨S, inferInstance, cells, plane, fun a j => a.val (.inr j), ?_, ?_, ?_, on_plane, ?_⟩
  · intro a
    refine ⟨AffineArrangement.isClosed_closedChamber equation a.val,
      AffineArrangement.convex_closedChamber equation a.val, ?_⟩
    rw [AffineArrangement.interior_closedChamber equation a.val (nonempty a.val a.property).1]
    exact (nonempty a.val a.property).1
  · intro a b different
    exact AffineArrangement.disjoint_chamber_interiors equation
      (nonempty a.val a.property).1 (nonempty b.val b.property).1
      (fun same => different (Subtype.ext same))
  · rw [cover]
    ext p
    simp only [cells, Set.mem_iUnion, Subtype.exists, exists_prop]
  · intro a p hp j
    exact hp (.inr j)

end Unfoldings.AffineEnvelope
