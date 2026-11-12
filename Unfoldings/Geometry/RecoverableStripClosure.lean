module

public import Unfoldings.Geometry.RecoverableStripPinches
public import Unfoldings.Geometry.MonotoneStripSlab
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Separation.Basic

/-! Finite coherent pinches leave every bank point before an active height in the strip closure. -/

@[expose] public section

namespace Unfoldings

theorem Icc_subset_closure_Ioo_sdiff_finite {a b : ℝ} (ordered : a < b)
    {exception : Set ℝ} (finite : exception.Finite) :
    Set.Icc a b ⊆ closure (Set.Ioo a b \ exception) := by
  have dense : Dense exceptionᶜ := by
    simpa only [← Set.compl_eq_univ_sdiff] using dense_univ.sdiff_finite finite
  have inside : Set.Ioo a b ⊆ closure (Set.Ioo a b \ exception) :=
    dense.open_subset_closure_inter isOpen_Ioo
  calc
    Set.Icc a b = closure (Set.Ioo a b) := (closure_Ioo ordered.ne).symm
    _ ⊆ closure (closure (Set.Ioo a b \ exception)) := closure_mono inside
    _ = _ := closure_closure

namespace MonotoneStrip

variable (S : MonotoneStrip)

theorem strict_height_pos_of_source (first : S.lower.coordinate 0 = 0)
    (last : S.upper.coordinate 0 = 0) {z : ℂ} (member : z ∈ S.strictCarrier)
    (nonnegative : 0 ≤ z.re + z.im) : 0 < z.re + z.im := by
  by_contra nonpositive
  have zero : z.re + z.im = 0 := le_antisymm (le_of_not_gt nonpositive) nonnegative
  have impossible := member.1.trans member.2
  rw [zero, first, last] at impossible
  exact lt_irrefl _ impossible

theorem bank_points_mem_closure_of_width {h a b : ℝ} (slab : h ∈ Set.Icc a b)
    (width : S.lower.coordinate h < S.upper.coordinate h) :
    S.lower.point h ∈ closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b} ∧
      S.upper.point h ∈ closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b} := by
  let f := fun x : ℝ => (⟨x, h - x⟩ : ℂ)
  have continuous : Continuous f := by
    have parts := Complex.continuous_ofReal.add
      ((Complex.continuous_ofReal.comp ((continuous_const (y := h)).sub continuous_id)).mul
        (continuous_const (y := Complex.I)))
    convert parts using 1
    ext x
    apply Complex.ext <;> simp [f]
  have subset : f '' Set.Ioo (S.lower.coordinate h) (S.upper.coordinate h) ⊆
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b} := by
    rintro z ⟨x, bounds, rfl⟩
    have height : (f x).re + (f x).im = h := by change x + (h - x) = h; ring
    refine ⟨?_, height ▸ slab⟩
    change S.lower.coordinate ((f x).re + (f x).im) < x ∧
      x < S.upper.coordinate ((f x).re + (f x).im)
    rwa [height]
  have endpoints : S.lower.coordinate h ∈
      closure (Set.Ioo (S.lower.coordinate h) (S.upper.coordinate h)) ∧
      S.upper.coordinate h ∈ closure (Set.Ioo (S.lower.coordinate h) (S.upper.coordinate h)) := by
    rw [closure_Ioo width.ne]
    exact ⟨⟨le_rfl, width.le⟩, ⟨width.le, le_rfl⟩⟩
  have approach (x : ℝ) (member : x ∈ closure
      (Set.Ioo (S.lower.coordinate h) (S.upper.coordinate h))) :
      f x ∈ closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b} :=
    closure_mono subset (continuous.continuousAt.continuousWithinAt.mem_closure_image member)
  exact ⟨approach _ endpoints.1, approach _ endpoints.2⟩

/-- Every bank point up to an active positive-width height is approached from actual strict
interiors. This includes isolated leaf pinches and the source; no permanently collapsed
continuation beyond the active height is asserted to have such a trace. -/
theorem bank_points_mem_closure_before_active_height {E : Set ℂ} (finite : E.Finite)
    {a k b : ℝ} (pinches : S.RecoverablePinchesIn E a b) (start : a < k) (finish : k ≤ b)
    (width : S.lower.coordinate k < S.upper.coordinate k) :
    ∀ h ∈ Set.Icc a k,
      S.lower.point h ∈ closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b} ∧
        S.upper.point h ∈ closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b} := by
  let exception := (fun z : ℂ => z.re + z.im) '' E
  let domain := {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b}
  let good := {h | S.lower.point h ∈ closure domain ∧ S.upper.point h ∈ closure domain}
  have closed : IsClosed good :=
    (isClosed_closure.preimage S.lower.point_continuous).inter
      (isClosed_closure.preimage S.upper.point_continuous)
  have inside : Set.Ioo a k \ exception ⊆ good := by
    intro h member
    have slab : h ∈ Set.Icc a b := ⟨member.1.1.le, member.1.2.le.trans finish⟩
    have positive : S.lower.coordinate h < S.upper.coordinate h := by
      by_contra different
      have collapsed : S.lower.coordinate h = S.upper.coordinate h :=
        le_antisymm (S.ordered h) (le_of_not_gt different)
      have coherent := pinches h slab collapsed k ⟨member.1.2.le, finish⟩ width
      exact member.2 ⟨S.lower.point h, coherent, S.lower.point_height h⟩
    exact S.bank_points_mem_closure_of_width slab positive
  exact (Icc_subset_closure_Ioo_sdiff_finite start (finite.image _)).trans
    (closure_minimal inside closed)

theorem source_mem_closure_before_active_height {E : Set ℂ} (finite : E.Finite)
    {k b : ℝ} (first : S.lower.coordinate 0 = 0) (pinches : S.RecoverablePinchesIn E 0 b)
    (start : 0 < k) (finish : k ≤ b) (width : S.lower.coordinate k < S.upper.coordinate k) :
    (0 : ℂ) ∈ closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 b} := by
  have lower := (S.bank_points_mem_closure_before_active_height finite pinches start finish width
    0 ⟨le_rfl, start.le⟩).1
  have point : S.lower.point 0 = (0 : ℂ) := by
    apply Complex.ext
    · exact first
    · change 0 - S.lower.coordinate 0 = 0
      rw [first, sub_self]
  rwa [point] at lower

end MonotoneStrip
end Unfoldings
