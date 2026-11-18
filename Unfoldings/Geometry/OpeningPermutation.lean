module

public import Unfoldings.Geometry.PolygonalRayOpening
public import Unfoldings.Geometry.ChainExt

/-! Reordering actual suffix rotations retains every final bank point and its infinite tail. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {n : ℕ}

/-- Actual suffix rotations fix the original starting vertex through the entire history. -/
@[simp] theorem openings_start (P : PolygonalChain ℂ n) (events : List (Opening n)) :
    (P.openings events).vertex 0 = P.vertex 0 := by
  induction events generalizing P with
  | nil => rfl
  | cons event events ih =>
    exact (ih (P.rotateSuffix event.hinge event.angle)).trans
      (P.rotateSuffix_start event.hinge event.angle)

/-- Equality of the unreduced link corrections preserves the entire opened chain. -/
theorem openings_eq_of_heading_eq (P : PolygonalChain ℂ n) (first last : List (Opening n))
    (headings : ∀ i, openingHeading first i = openingHeading last i) :
    P.openings first = P.openings last := by
  apply eq_of_start_edge_eq
  · rw [P.openings_start, P.openings_start]
  · intro i
    rw [P.openings_edge, P.openings_edge, headings]

/-- Planar joint rotations commute even with their actual updated hinge translations. -/
theorem openings_eq_of_perm (P : PolygonalChain ℂ n) {first last : List (Opening n)}
    (permuted : first.Perm last) : P.openings first = P.openings last := by
  apply P.openings_eq_of_heading_eq first last
  intro i
  exact (permuted.map (fun event =>
    if event.hinge ≤ i.castSucc then event.angle else 0)).sum_eq

end Unfoldings.PolygonalChain

namespace Unfoldings.PolygonalRay

open PolygonalChain

variable {n : ℕ}

/-- Exact unreduced finite and tail headings retain every point of the complete opened bank. -/
theorem openings_eq_of_heading_tail_eq (R : PolygonalRay ℂ n)
    (first last : List (Opening n))
    (headings : ∀ i, openingHeading first i = openingHeading last i)
    (tail : openingTailHeading first = openingTailHeading last) :
    R.openings first = R.openings last := by
  have chains : (R.openings first).chain = (R.openings last).chain := by
    rw [R.openings_chain, R.openings_chain]
    exact R.chain.openings_eq_of_heading_eq first last headings
  have directions : (R.openings first).direction = (R.openings last).direction := by
    rw [R.openings_direction, R.openings_direction, tail]
  cases hfirst : R.openings first with
  | mk firstChain firstDirection =>
    cases hlast : R.openings last with
    | mk lastChain lastDirection =>
      simp only [hfirst, hlast] at chains directions
      cases chains
      cases directions
      rfl

/-- The infinite tail retains both its initial point and its true direction after reordering. -/
theorem openings_eq_of_perm (R : PolygonalRay ℂ n) {first last : List (Opening n)}
    (permuted : first.Perm last) : R.openings first = R.openings last := by
  apply R.openings_eq_of_heading_tail_eq first last
  · intro i
    exact (permuted.map (fun event =>
      if event.hinge ≤ i.castSucc then event.angle else 0)).sum_eq
  · exact (permuted.map Opening.angle).sum_eq

/-- The fresh positive source charge may be moved first for the Jordan-gap proof. -/
theorem openings_append_source (R : PolygonalRay ℂ n) (events : List (Opening n)) (angle : ℝ) :
    R.openings (events ++ [⟨0, angle⟩]) = R.openings (⟨0, angle⟩ :: events) :=
  R.openings_eq_of_perm (List.perm_append_singleton _ _)

end Unfoldings.PolygonalRay
