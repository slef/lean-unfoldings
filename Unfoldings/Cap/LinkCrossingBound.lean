module

public import Unfoldings.Cap.GermCrossing
public import Unfoldings.Polyhedron.AngularLink

/-! Convexity bounds the actual cyclic vertex link by two hemisphere crossings. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {v : C.Vertex Set.univ} {m : ℕ} (c : (C.linkSystem Set.univ v).Chain m)

/-- This is derived from supporting planes and disjoint projected faces, with no crossing input. -/
theorem card_link_crossings_le_two
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (covers : ∀ p, c.Visited p) (n : Space) (upward : 0 < n 2) :
    Fintype.card {i : Fin (m + 1) // inner ℝ n (K.folding.germDirection (c.point i).val) *
      inner ℝ n (K.folding.germDirection (c.point (finRotate (m + 1) i)).val) < 0} ≤ 2 := by
  classical
  let ray (i : Fin (m + 1)) := K.folding.germDirection (c.point i).val
  let I := {i : Fin (m + 1) // inner ℝ n (ray i) * inner ℝ n (ray (finRotate (m + 1) i)) < 0}
  change Fintype.card I ≤ 2
  by_cases positive : ∃ i, 0 < inner ℝ n (ray i)
  · obtain ⟨j, hj⟩ := positive
    let q := K.projectedGermRay (c.point j)
    have strict (a : C.CornerAt Set.univ v) : 0 < K.germUpperForm v n a q :=
      hj.trans_le (K.germUpperForm_bound n upward a (c.point j))
    have witnesses (i : I) : ∃ z : Plane, z ≠ 0 ∧
        z ∈ strictRayCone (K.projectedGermRay (c.point i.val))
          (K.projectedGermRay (c.point (finRotate (m + 1) i.val))) ∧
        (∀ a : C.CornerAt Set.univ v, 0 ≤ K.germUpperForm v n a z) ∧
        K.germUpperForm v n ⟨(c.point i.val).val.1, (c.point i.val).property⟩ z = 0 := by
      have crossing := i.property
      change inner ℝ n (K.folding.germDirection (c.point i.val).val) *
        inner ℝ n (K.folding.germDirection (c.point (finRotate (m + 1) i.val)).val) < 0 at crossing
      rw [← K.folding.germDirection_chain_rotates c closes] at crossing
      obtain ⟨z, hne, member, supports, active⟩ :=
        K.exists_germ_crossing_point n upward (c.point i.val) crossing
      rw [K.projectedGermRay_chain_rotates c closes] at member
      exact ⟨z, hne, member, supports, active⟩
    choose point genuine member supported active using witnesses
    apply card_le_two_of_supported_boundary (K.germUpperForm v n) q strict
      (fun i : I => K.projectedGermRay (c.point i.val))
      (fun i : I => K.projectedGermRay (c.point (finRotate (m + 1) i.val))) point
      (fun i j different => K.projectedLinkFan_cones_disjoint c closes covers
        (fun equal => different (Subtype.ext equal))) genuine member supported
    intro i
    exact ⟨⟨(c.point i.val).val.1, (c.point i.val).property⟩, active i⟩
  · have empty : IsEmpty I := ⟨fun i => by
      rcases mul_neg_iff.mp i.property with pair | pair
      · exact positive ⟨i.val, pair.1⟩
      · exact positive ⟨finRotate (m + 1) i.val, pair.2⟩⟩
    simp only [Fintype.card_of_isEmpty, Nat.zero_le]

end Unfoldings.ConvexCap
