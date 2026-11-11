module

public import Unfoldings.Geometry.CyclicDisplacements
public import Unfoldings.Topology.CyclicRegion

/-! A cyclic interval with equal endpoint labels contains both separator crossings or neither. -/

@[expose] public section

namespace Unfoldings

variable {X : Type*} [Finite X]

/-- Discrete integration of a second region's indicator pairs its two crossing banks.
This applies to partial contour excursions whose endpoint copies have the same original vertex. -/
theorem cyclic_region_crossings_paired (next : Equiv.Perm X) (region label : X → Prop)
    (a b e f : X) (region_ne : a ≠ b) (label_ne : e ≠ f)
    (region_enters : ¬ region a ∧ region (next a))
    (region_leaves : region b ∧ ¬ region (next b))
    (region_stable : ∀ i, i ≠ a → i ≠ b → (region (next i) ↔ region i))
    (label_enters : ¬ label e ∧ label (next e))
    (label_leaves : label f ∧ ¬ label (next f))
    (label_stable : ∀ i, i ≠ e → i ≠ f → (label (next i) ↔ label i))
    (endpoints : label (next a) ↔ label (next b)) : region e ↔ region f := by
  classical
  let := Fintype.ofFinite X
  let indicator (i : X) : ℤ := if label i then 1 else 0
  have delta (i : X) : indicator (next i) - indicator i =
      (if i = e then 1 else 0) - (if i = f then 1 else 0) := by
    by_cases first : i = e
    · subst i
      simp [indicator, label_enters.1, label_enters.2, label_ne]
    · by_cases last : i = f
      · subst i
        simp [indicator, label_leaves.1, label_leaves.2, label_ne.symm]
      · simp [indicator, label_stable i first last, first, last]
  have weighted (i : X) :
      (if region i then indicator (next i) - indicator i else 0) =
        (if i = e then (if region e then 1 else 0) else 0) -
          (if i = f then (if region f then 1 else 0) else 0) := by
    rw [delta]
    by_cases first : i = e
    · subst i
      simp [label_ne]
    · by_cases last : i = f
      · subst i
        by_cases selected : region f <;> simp [label_ne.symm, selected]
      · simp [first, last]
  have sum := displacement_of_two_region_exits next region indicator a b region_ne
    region_enters region_leaves region_stable
  have same : indicator (next b) = indicator (next a) := by
    simp only [indicator, endpoints]
  rw [same, sub_self] at sum
  simp_rw [weighted] at sum
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at sum
  by_cases first : region e <;> by_cases last : region f <;> simp_all

end Unfoldings
