module

public import Unfoldings.Geometry.RadialClosureContacts

/-! Nontrivial radial bank arcs have genuine interior witnesses and only two bank corners. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n) (q c : Plane)

/-- The literal three-link arc complementary to the radial bank. -/
def radialClosingArc : Set Plane :=
  (segment ℝ (P.vertex (Fin.last n)) c ∪ segment ℝ c q) ∪ segment ℝ q (P.vertex 0)

theorem radialClosingArc_closed : IsClosed (P.radialClosingArc q c) :=
  (((compact_segment _ _).isClosed.union (compact_segment _ _).isClosed).union
    (compact_segment _ _).isClosed)

theorem radial_source_not_on_bank (radial : P.RadialFrom q 0)
    (initial : 0 < dist q (P.vertex 0)) : q ∉ Set.range P.path := by
  intro member
  have lower := (P.path_radius_bounds q radial member).1
  rw [dist_self] at lower
  exact not_le_of_gt initial lower

theorem closing_corner_not_on_bank (height : Plane →ₗ[ℝ] ℝ)
    (supported : ∀ z ∈ Set.range P.path, 0 ≤ height (z - q))
    (outside : height (c - q) < 0) : c ∉ Set.range P.path :=
  fun member => not_le_of_gt outside (supported c member)

open Classical in
/-- The only marked closing corners on the actual bank are its own endpoints. -/
theorem radialClosingCorners_on_bank (radial : P.RadialFrom q 0)
    (initial : 0 < dist q (P.vertex 0)) (height : Plane →ₗ[ℝ] ℝ)
    (supported : ∀ z ∈ Set.range P.path, 0 ≤ height (z - q))
    (outside : height (c - q) < 0) {z : Plane} (on_bank : z ∈ Set.range P.path) :
    z ∈ radialClosingCorners q (P.vertex 0) (P.vertex (Fin.last n)) c ↔
      z ∈ ({P.vertex 0, P.vertex (Fin.last n)} : Finset Plane) := by
  simp only [radialClosingCorners, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (first | last | source | corner)
    · exact Or.inl first
    · exact Or.inr last
    · exact (P.radial_source_not_on_bank q radial initial (source ▸ on_bank)).elim
    · exact (P.closing_corner_not_on_bank q c height supported outside (corner ▸ on_bank)).elim
  · rintro (first | last)
    · exact Or.inl first
    · exact Or.inr (Or.inl last)

/-- Strict radial progress supplies a bank point away from the entire closing arc. -/
theorem exists_radial_bank_interior (radial : P.RadialFrom q 0)
    (initial : 0 < dist q (P.vertex 0))
    (progress : dist q (P.vertex 0) < dist q (P.vertex (Fin.last n)))
    (height : Plane →ₗ[ℝ] ℝ) (supported : ∀ z ∈ Set.range P.path, 0 ≤ height (z - q))
    (outside : height (c - q) < 0)
    (outward : 0 < inner ℝ (P.vertex (Fin.last n) - q) (c - P.vertex (Fin.last n))) :
    ∃ z ∈ P.threeSegmentClosure q c, z ∉ P.radialClosingArc q c := by
  let r := (dist q (P.vertex 0) + dist q (P.vertex (Fin.last n))) / 2
  have first : dist q (P.vertex 0) < r := by dsimp [r]; linarith
  have last : r < dist q (P.vertex (Fin.last n)) := by dsimp [r]; linarith
  obtain ⟨t, equal⟩ := (P.path_radius_range q radial).symm.subset ⟨first.le, last.le⟩
  change dist q (P.path t) = r at equal
  refine ⟨P.path t, Or.inl (Set.mem_range_self t), ?_⟩
  intro member
  have contact := (P.radial_bank_closing_contacts q c radial initial height supported outside
    outward).subset ⟨Set.mem_range_self t, member⟩
  rcases contact with at_first | at_last
  · have radius := congrArg (dist q) at_first
    rw [equal] at radius
    exact first.ne radius.symm
  · have radius := congrArg (dist q) (Set.mem_singleton_iff.mp at_last)
    rw [equal] at radius
    exact last.ne radius

end Unfoldings.PolygonalChain
