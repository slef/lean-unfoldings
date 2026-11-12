module

public import Unfoldings.Geometry.MonotoneStripTopology

/-! Localize approached strip points to open height slabs and find later active heights. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

/-- At an interior height, closed and open slab conventions give the same
approached points. No positive-width hypothesis at the tested point is needed. -/
theorem mem_closure_openSlab_of_height {a b : ℝ} {z : ℂ}
    (closed : z ∈ closure {w | w ∈ S.strictCarrier ∧ w.re + w.im ∈ Set.Icc a b})
    (height : z.re + z.im ∈ Set.Ioo a b) : z ∈ closure (S.openSlab a b) := by
  apply mem_closure_iff.mpr
  intro O opened member
  have height_open : IsOpen {w : ℂ | w.re + w.im ∈ Set.Ioo a b} :=
    isOpen_Ioo.preimage (Complex.continuous_re.add Complex.continuous_im)
  obtain ⟨w, ⟨in_O, in_height⟩, strict, _⟩ := mem_closure_iff.mp closed
    (O ∩ {w : ℂ | w.re + w.im ∈ Set.Ioo a b}) (opened.inter height_open) ⟨member, height⟩
  exact ⟨w, in_O, strict, in_height⟩

/-- An approached point strictly above a tested level supplies an actual open
strip point above that level, including when the endpoint is a terminal pinch. -/
theorem exists_openSlab_above_of_closed {a b h : ℝ} {z : ℂ}
    (closed : z ∈ closure (S.openSlab a b)) (before : h < z.re + z.im) :
    ∃ w ∈ S.openSlab a b, h < w.re + w.im := by
  obtain ⟨w, above, member⟩ := mem_closure_iff.mp closed
    {w : ℂ | h < w.re + w.im}
    (isOpen_lt continuous_const (Complex.continuous_re.add Complex.continuous_im)) before
  exact ⟨w, member, above⟩

end Unfoldings.MonotoneStrip
