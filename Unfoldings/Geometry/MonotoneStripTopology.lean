module

public import Unfoldings.Geometry.MonotoneStripSubdivision
public import Unfoldings.Geometry.MonotoneStripSlab
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Bounded open strips have compact closure and only their banks and end levels as frontier. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

def openSlab (a b : ℝ) : Set ℂ :=
  {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Ioo a b}

theorem isOpen_strictCarrier : IsOpen S.strictCarrier :=
  (isOpen_lt (S.lower.continuous.comp (Complex.continuous_re.add Complex.continuous_im))
    Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re
      (S.upper.continuous.comp (Complex.continuous_re.add Complex.continuous_im)))

theorem isClosed_carrier : IsClosed S.carrier :=
  (isClosed_le (S.lower.continuous.comp (Complex.continuous_re.add Complex.continuous_im))
    Complex.continuous_re).inter
    (isClosed_le Complex.continuous_re
      (S.upper.continuous.comp (Complex.continuous_re.add Complex.continuous_im)))

theorem isOpen_openSlab (a b : ℝ) : IsOpen (S.openSlab a b) :=
  S.isOpen_strictCarrier.inter
    (isOpen_Ioo.preimage (Complex.continuous_re.add Complex.continuous_im))

theorem isClosed_boundedCarrier (a b : ℝ) : IsClosed (S.boundedCarrier a b) :=
  S.isClosed_carrier.inter
    (isClosed_Icc.preimage (Complex.continuous_re.add Complex.continuous_im))

theorem isCompact_boundedCarrier (a b : ℝ) : IsCompact (S.boundedCarrier a b) := by
  let l := S.lower.coordinate a
  let u := S.upper.coordinate b
  let R := 2 * (|l| + |u|) + |a| + |b|
  apply (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset (S.isClosed_boundedCarrier a b)
  intro z member
  have lower := (S.lower.coordinate_mono member.2.1).trans member.1.1
  have upper := member.1.2.trans (S.upper.coordinate_mono member.2.2)
  change l ≤ z.re at lower
  change z.re ≤ u at upper
  have real : |z.re| ≤ |l| + |u| := abs_le.mpr ⟨by
    linarith [neg_abs_le l, abs_nonneg u], by linarith [le_abs_self u, abs_nonneg l]⟩
  have imaginary : |z.im| ≤ |a| + |b| + |l| + |u| := abs_le.mpr ⟨by
    linarith [member.2.1, neg_abs_le a, le_abs_self u, abs_nonneg b, abs_nonneg l], by
    linarith [member.2.2, le_abs_self b, neg_abs_le l, abs_nonneg a, abs_nonneg u]⟩
  have bound := Complex.norm_le_abs_re_add_abs_im z
  rw [Metric.mem_closedBall, dist_zero_right]
  dsimp only [R]
  linarith

theorem closure_openSlab_subset (a b : ℝ) : closure (S.openSlab a b) ⊆ S.boundedCarrier a b :=
  closure_minimal
    (fun _ member => ⟨⟨member.1.1.le, member.1.2.le⟩, member.2.1.le, member.2.2.le⟩)
    (S.isClosed_boundedCarrier a b)

theorem isCompact_closure_openSlab (a b : ℝ) : IsCompact (closure (S.openSlab a b)) :=
  (S.isCompact_boundedCarrier a b).of_isClosed_subset isClosed_closure
    (S.closure_openSlab_subset a b)

/-- Reopening pinches are included on the banks. No extra frontier component can
occur in the strict interior of the physical slab. -/
theorem frontier_openSlab_cases (a b : ℝ) {z : ℂ} (boundary : z ∈ frontier (S.openSlab a b)) :
    z = S.lower.point (z.re + z.im) ∨ z = S.upper.point (z.re + z.im) ∨
      z.re + z.im = a ∨ z.re + z.im = b := by
  have member := S.closure_openSlab_subset a b boundary.1
  by_cases lower : S.lower.coordinate (z.re + z.im) = z.re
  · exact Or.inl (S.lower.point_eq_of_coordinate z lower).symm
  by_cases upper : S.upper.coordinate (z.re + z.im) = z.re
  · exact Or.inr (Or.inl (S.upper.point_eq_of_coordinate z upper).symm)
  by_cases first : z.re + z.im = a
  · exact Or.inr (Or.inr (Or.inl first))
  by_cases last : z.re + z.im = b
  · exact Or.inr (Or.inr (Or.inr last))
  have inside : z ∈ S.openSlab a b :=
    ⟨⟨lt_of_le_of_ne member.1.1 lower, lt_of_le_of_ne member.1.2 (Ne.symm upper)⟩,
      lt_of_le_of_ne member.2.1 (Ne.symm first), lt_of_le_of_ne member.2.2 last⟩
  exact (boundary.2 ((S.isOpen_openSlab a b).interior_eq.symm ▸ inside)).elim

end Unfoldings.MonotoneStrip
