module

public import Unfoldings.Cap.JordanCyclicRolling
public import Unfoldings.Cap.RadialBankTurnComparison
public import Unfoldings.Geometry.RadialBankInterior

/-! Geometric radial comparison bounds the actual unreduced intrinsic bank rolling. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {n : ℕ} (P : PolygonalChain Plane n) (q c : Plane)
  (jordan : Schoenflies.IsJordanCurve (P.threeSegmentClosure q c))
  (contains : P.threeSegmentClosure q c ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) (P.threeSegmentClosure q c))

include jordan contains avoids in
open Classical in
/-- The actual endpoint copies determine an oriented rolling span and its real heading bound.
Traversal direction and the internal bank interval are derived from radial closure geometry. -/
theorem exists_radial_bank_rolling_comparison_of_geometric_budget
    (radial : P.RadialFrom q 0) (initial : 0 < dist q (P.vertex 0))
    (progress : dist q (P.vertex 0) < dist q (P.vertex (Fin.last n)))
    (height : Plane →ₗ[ℝ] ℝ) (supported : ∀ z ∈ Set.range P.path, 0 ≤ height (z - q))
    (outside : height (c - q) < 0)
    (outward : 0 < inner ℝ (P.vertex (Fin.last n) - q) (c - P.vertex (Fin.last n)))
    (first_occurs : ∃ i, K.jordanBankPosition jordan contains avoids i = P.vertex 0)
    (last_occurs : ∃ i, K.jordanBankPosition jordan contains avoids i = P.vertex (Fin.last n))
    {B : ℝ}
    (budget : |∑ i ∈ K.jordanGeometricBankIndices jordan contains avoids (Set.range P.path)
        (radialClosingCorners q (P.vertex 0) (P.vertex (Fin.last n)) c),
      K.jordanContourTurnError jordan contains avoids i| ≤ B) :
    ∃ first last : Fin ((K.jordanContour jordan contains avoids).length + 1),
      ({K.jordanBankPosition jordan contains avoids first,
        K.jordanBankPosition jordan contains avoids last} : Finset Plane) =
          {P.vertex 0, P.vertex (Fin.last n)} ∧
      K.jordanContourBankOn jordan contains avoids (Set.range P.path) first ∧
      ¬ K.jordanContourBankOn jordan contains avoids (Set.range P.path) last ∧
      |K.jordanCyclicRollHeadingError jordan contains avoids first
        ⟨((finCycle first).symm last).val - 1, by omega⟩| ≤
          B := by
  let bank := Set.range P.path
  let rest := P.radialClosingArc q c
  let pos := K.jordanBankPosition jordan contains avoids
  have bank_closed : IsClosed bank := (isCompact_range P.path.continuous).isClosed
  have rest_closed : IsClosed rest := P.radialClosingArc_closed q c
  have cover : P.threeSegmentClosure q c ⊆ bank ∪ rest := Set.Subset.rfl
  have contacts : bank ∩ rest = {P.vertex 0, P.vertex (Fin.last n)} :=
    P.radial_bank_closing_contacts q c radial initial height supported outside outward
  obtain ⟨a, at_a⟩ := first_occurs
  obtain ⟨b, at_b⟩ := last_occurs
  change pos a = P.vertex 0 at at_a
  change pos b = P.vertex (Fin.last n) at at_b
  have actual_contacts : bank ∩ rest ⊆ {pos a, pos b} := by
    rw [at_a, at_b]
    exact contacts.subset
  have opposite := K.jordanContourBankOn_contacts_complementary jordan contains avoids
    bank_closed rest_closed cover a b actual_contacts
    (P.exists_radial_bank_interior q c radial initial progress height supported outside outward)
    ⟨c, Or.inr (Or.inl (Or.inl (right_mem_segment ℝ _ _))),
      P.closing_corner_not_on_bank q c height supported outside⟩
  have bound_for (first last)
      (ends_eq : ({pos first, pos last} : Finset Plane) = {P.vertex 0, P.vertex (Fin.last n)})
      (on_first : K.jordanContourBankOn jordan contains avoids bank first)
      (off_last : ¬ K.jordanContourBankOn jordan contains avoids bank last) :
      |K.jordanCyclicRollHeadingError jordan contains avoids first
        ⟨((finCycle first).symm last).val - 1, by omega⟩| ≤
          B := by
    have span_contacts : bank ∩ rest ⊆ {pos first, pos last} := by
      intro z member
      have endpoint := contacts.subset member
      have marked : z ∈ ({P.vertex 0, P.vertex (Fin.last n)} : Finset Plane) := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] using endpoint
      rw [← ends_eq] at marked
      simpa only [Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] using marked
    rw [K.jordanCyclicRollHeadingError_eq_bank_sum jordan contains avoids bank_closed rest_closed
      cover first last span_contacts on_first off_last]
    change |∑ j ∈ K.jordanGeometricBankIndices jordan contains avoids bank {pos first, pos last},
      K.jordanContourTurnError jordan contains avoids j| ≤ _
    rw [ends_eq, ← K.jordanGeometricBankIndices_congr_corners jordan contains avoids bank
      (radialClosingCorners q (P.vertex 0) (P.vertex (Fin.last n)) c)
      {P.vertex 0, P.vertex (Fin.last n)}
      (fun z member => P.radialClosingCorners_on_bank q c radial initial height supported outside
        member)]
    exact budget
  by_cases on_a : K.jordanContourBankOn jordan contains avoids bank a
  · have off_b := opposite.mp on_a
    have ends_eq : ({pos a, pos b} : Finset Plane) = {P.vertex 0, P.vertex (Fin.last n)} := by
      rw [at_a, at_b]
    exact ⟨a, b, ends_eq, on_a, off_b, bound_for a b ends_eq on_a off_b⟩
  · have on_b : K.jordanContourBankOn jordan contains avoids bank b := by
      by_contra off_b
      exact on_a (opposite.mpr off_b)
    have ends_eq : ({pos b, pos a} : Finset Plane) = {P.vertex 0, P.vertex (Fin.last n)} := by
      rw [at_a, at_b, Finset.pair_comm]
    exact ⟨b, a, ends_eq, on_b, on_a, bound_for b a ends_eq on_b on_a⟩

include jordan contains avoids in
open Classical in
/-- The actual endpoint copies determine an oriented rolling span and its real heading bound.
Traversal direction and the internal bank interval are derived from radial closure geometry. -/
theorem exists_radial_bank_rolling_comparison
    (inside : P.threeSegmentClosure q c ⊆ interior K.footprint)
    (radial : P.RadialFrom q 0) (initial : 0 < dist q (P.vertex 0))
    (progress : dist q (P.vertex 0) < dist q (P.vertex (Fin.last n)))
    (height : Plane →ₗ[ℝ] ℝ) (supported : ∀ z ∈ Set.range P.path, 0 ≤ height (z - q))
    (outside : height (c - q) < 0)
    (outward : 0 < inner ℝ (P.vertex (Fin.last n) - q) (c - P.vertex (Fin.last n)))
    (first_occurs : ∃ i, K.jordanBankPosition jordan contains avoids i = P.vertex 0)
    (last_occurs : ∃ i, K.jordanBankPosition jordan contains avoids i = P.vertex (Fin.last n))
    {ε φ : ℝ} (error_nonnegative : 0 ≤ ε) (error : K.RelativeCornerAngleError ε)
    (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    ∃ first last : Fin ((K.jordanContour jordan contains avoids).length + 1),
      ({K.jordanBankPosition jordan contains avoids first,
        K.jordanBankPosition jordan contains avoids last} : Finset Plane) =
          {P.vertex 0, P.vertex (Fin.last n)} ∧
      K.jordanContourBankOn jordan contains avoids (Set.range P.path) first ∧
      ¬ K.jordanContourBankOn jordan contains avoids (Set.range P.path) last ∧
      |K.jordanCyclicRollHeadingError jordan contains avoids first
        ⟨((finCycle first).symm last).val - 1, by omega⟩| ≤
          C.totalInteriorAngularDefect Set.univ + 6 * φ + 8 * Real.pi * ε := by
  apply K.exists_radial_bank_rolling_comparison_of_geometric_budget P q c jordan contains avoids
    radial initial progress height supported outside outward first_occurs last_occurs
  exact K.abs_radial_bank_turn_error_le P q c jordan contains avoids inside initial progress height
    (supported _ ⟨0, P.path.source⟩) (supported _ ⟨1, P.path.target⟩) outside outward
    error_nonnegative error nonnegative small tilt

end Unfoldings.ConvexCap
