module

public import Unfoldings.Roof.LinkCrossingBound
public import Unfoldings.Roof.GermNormalCone
public import Unfoldings.Geometry.CyclicSignChanges

/-! The genuine roof link has zero or two crossings according to its actual normal cone. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open scoped ENNReal

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {v : C.Vertex Set.univ} {m : ℕ} (c : (C.linkSystem Set.univ v).Chain m)

open scoped Classical in
/-- Convexity, local incidence, and the actual cyclic order discharge the crossing count. -/
theorem link_crossings_eq_zero_or_two
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (covers : ∀ p, c.Visited p)
    (inside : K.projectedVertex v ∈ interior K.footprint)
    (n : Space) (unit : ‖n‖ = 1) (upward : 0 < n 2)
    (nonzero : ∀ p : C.LinkGerm Set.univ v, inner ℝ n (K.folding.germDirection p.val) ≠ 0) :
    angularCrossings (fun i => K.folding.germDirection (c.point i).val) (finRotate (m + 1)) n =
      if n ∈ K.sphericalNormalPolygon v then 0 else 2 := by
  classical
  rw [angularCrossings_eq_card]
  by_cases present : n ∈ K.sphericalNormalPolygon v
  · rw [ite_eq_left present]
    have nonpos := (K.mem_sphericalNormalPolygon_iff_germs_nonpos inside n unit upward).mp present
    have empty : IsEmpty {i : Fin (m + 1) //
        inner ℝ n (K.folding.germDirection (c.point i).val) *
          inner ℝ n (K.folding.germDirection (c.point (finRotate (m + 1) i)).val) < 0} :=
      ⟨fun i => (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos
        (nonpos (c.point i.val)) (nonpos (c.point (finRotate (m + 1) i.val))))) i.property⟩
    simp only [Fintype.card_of_isEmpty, Nat.cast_zero]
  · rw [ite_eq_right present]
    have positive : ∃ p : C.LinkGerm Set.univ v,
        0 < inner ℝ n (K.folding.germDirection p.val) := by
      by_contra none
      push Not at none
      exact present ((K.mem_sphericalNormalPolygon_iff_germs_nonpos inside n unit upward).mpr none)
    have negative := K.exists_germ_inner_neg inside n upward nonzero
    have cardinality := card_cyclic_sign_changes_eq_two
      (fun i => inner ℝ n (K.folding.germDirection (c.point i).val))
      (fun i => nonzero (c.point i))
      ((K.folding.exists_chain_germDirection_iff c closes covers
        (fun z => 0 < inner ℝ n z)).mpr positive)
      ((K.folding.exists_chain_germDirection_iff c closes covers
        (fun z => inner ℝ n z < 0)).mpr negative)
      (K.card_link_crossings_le_two c closes covers n upward)
    rw [cardinality]
    norm_num

end Unfoldings.ConvexRoof
