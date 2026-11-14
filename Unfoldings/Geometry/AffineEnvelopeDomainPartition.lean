module

public import Unfoldings.Geometry.AffineEnvelopeTriangulation

/-! Triangulate a finite affine envelope over an independently prescribed compact polygon. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AffineEnvelope

universe u

variable {I J : Type u} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
  (support : I → Plane →ᵃ[ℝ] ℝ) (domain : J → Plane →ᵃ[ℝ] ℝ)

def domainPartitionEquation (Z : ℝ) :
    J ⊕ {p : I × I // support p.1 ≠ support p.2} → Plane →ᵃ[ℝ] ℝ :=
  Sum.elim (fun j => domain j - AffineMap.const ℝ Plane Z)
    (fun p => support p.val.1 - support p.val.2)

/-- Construct a finite triangle partition of the polygon on which the selected affine
envelope is affine on every triangle. The polygon need not be a level set of that envelope. -/
theorem exists_domain_triangle_partition {Z : ℝ} (compact : IsCompact (clip domain Z))
    {q : Plane} (higher : Z < height domain q) :
    ∃ (A : Type u) (_ : Finite A) (triangle : A → Triangle) (plane : A → I),
      clip domain Z = ⋃ a, (triangle a).carrier ∧
      Pairwise (fun a b =>
        Disjoint (interior (triangle a).carrier) (interior (triangle b).carrier)) ∧
      (∀ a p, p ∈ (triangle a).carrier → height support p = support (plane a) p) := by
  classical
  let equation := domainPartitionEquation support domain Z
  have proper : ∀ i, equation i ≠ 0 := by
    intro i
    cases i with
    | inl j =>
      intro zero
      have equal := congrArg (fun h : Plane →ᵃ[ℝ] ℝ => h q) zero
      change domain j q - Z = 0 at equal
      linarith [height_le domain q j]
    | inr pair => exact fun zero => pair.property (sub_eq_zero.mp zero)
  have nonempty : (interior (clip domain Z)).Nonempty := ⟨q, mem_interior_clip domain higher⟩
  have regular := ((convex_clip domain Z).closure_interior_eq_closure_of_nonempty_interior
    nonempty).trans compact.isClosed.closure_eq
  have boundary : ∀ p ∈ frontier (clip domain Z), ∃ i, equation i p = 0 := by
    intro p hp
    have level := height_eq_level_of_frontier domain hp
    obtain ⟨j, active⟩ := exists_height_eq domain p
    exact ⟨.inl j, by change domain j p - Z = 0; linarith⟩
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
        (signs a) in_chamber ((contained a).2 hx) (.inr ⟨(j, i), same⟩)
        (show 0 ≤ equation (.inr ⟨(j, i), same⟩) p from sub_nonneg.mpr order)
      exact sub_nonneg.mp sign
  choose plane on_plane using active
  exact ⟨A, finite, triangle, plane, cover, separated, on_plane⟩

end Unfoldings.AffineEnvelope
