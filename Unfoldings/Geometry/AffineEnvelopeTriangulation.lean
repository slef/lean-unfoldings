module

public import Unfoldings.Geometry.AffineEnvelope
public import Unfoldings.Geometry.ChamberTriangulation

/-! Finite triangle partitions of compact affine roofs respecting prescribed extra lines. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AffineEnvelope

universe u

variable {I J : Type u} [Fintype I] [Nonempty I] [Finite J]
  (support : I → Plane →ᵃ[ℝ] ℝ) (extra : J → Plane →ᵃ[ℝ] ℝ)

/-- Include clipping lines, nontrivial support-plane intersections, and extra constraints. -/
def partitionEquation (Z : ℝ) :
    I ⊕ ({p : I × I // support p.1 ≠ support p.2} ⊕ J) → Plane →ᵃ[ℝ] ℝ :=
  Sum.elim (fun i => support i - AffineMap.const ℝ Plane Z)
    (Sum.elim (fun p => support p.val.1 - support p.val.2) extra)

/-- Every compact section with a strictly higher point admits an actual finite triangle
partition on its active support planes, respecting any prescribed finite proper lines. -/
theorem exists_constrained_triangle_partition (proper_extra : ∀ j, extra j ≠ 0)
    {Z : ℝ} (compact : IsCompact (clip support Z)) {q : Plane} (higher : Z < height support q) :
    ∃ (A : Type u) (_ : Finite A) (triangle : A → Triangle) (plane : A → I) (signs : A → J → Bool),
      clip support Z = ⋃ a, (triangle a).carrier ∧
      Pairwise (fun a b =>
        Disjoint (interior (triangle a).carrier) (interior (triangle b).carrier)) ∧
      (∀ a p, p ∈ (triangle a).carrier → height support p = support (plane a) p) ∧
      (∀ a p, p ∈ (triangle a).carrier → ∀ j,
        0 ≤ AffineArrangement.signed (extra j) (signs a j) p) := by
  classical
  let equation := partitionEquation support extra Z
  have proper : ∀ i, equation i ≠ 0 := by
    intro i
    cases i with
    | inl i =>
      intro zero
      have equal := congrArg (fun h : Plane →ᵃ[ℝ] ℝ => h q) zero
      change support i q - Z = 0 at equal
      linarith [height_le support q i]
    | inr i =>
      cases i with
      | inl pair => exact fun zero => pair.property (sub_eq_zero.mp zero)
      | inr j => exact proper_extra j
  have nonempty : (interior (clip support Z)).Nonempty := ⟨q, mem_interior_clip support higher⟩
  have regular := ((convex_clip support Z).closure_interior_eq_closure_of_nonempty_interior
    nonempty).trans compact.isClosed.closure_eq
  have boundary : ∀ p ∈ frontier (clip support Z), ∃ i, equation i p = 0 := by
    intro p hp
    have level := height_eq_level_of_frontier support hp
    obtain ⟨i, active⟩ := exists_height_eq support p
    exact ⟨.inl i, by change support i p - Z = 0; linarith⟩
  obtain ⟨A, finite, triangle, signs, cover, separated, contained⟩ :=
    AffineArrangement.exists_finite_chamber_triangle_partition equation proper compact regular
      boundary
  have active (a : A) : ∃ i, ∀ p ∈ (triangle a).carrier, height support p = support i p := by
    obtain ⟨p, inside⟩ := (triangle a).interior_nonempty
    have in_chamber : p ∈ AffineArrangement.chamber equation (signs a) := by
      rw [← AffineArrangement.interior_closedChamber equation (signs a) (contained a).1]
      exact interior_mono (contained a).2 inside
    obtain ⟨i, realizes⟩ := exists_height_eq support p
    refine ⟨i, fun x hx => (mem_cell_iff support i x).mp (fun j => ?_)⟩
    by_cases same : support j = support i
    · exact (congrArg (fun h : Plane →ᵃ[ℝ] ℝ => h x) same).symm.le
    · have order := height_le support p j
      rw [realizes] at order
      have sign := AffineArrangement.closedChamber_nonnegative_of_chamber_nonnegative equation
        (signs a) in_chamber ((contained a).2 hx) (.inr (.inl ⟨(j, i), same⟩))
        (show 0 ≤ equation (.inr (.inl ⟨(j, i), same⟩)) p from sub_nonneg.mpr order)
      exact sub_nonneg.mp sign
  choose plane on_plane using active
  refine ⟨A, finite, triangle, plane, fun a j => signs a (.inr (.inr j)), cover, separated,
    on_plane, ?_⟩
  intro a p hp j
  exact (contained a).2 hp (.inr (.inr j))

end Unfoldings.AffineEnvelope
