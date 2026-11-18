module

public import Unfoldings.Metric.BankStackCurves

/-! Actual common bank metrics give equally paced typed consecutive seam curves. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {G Edge : Type*} {Parameter : Edge → Type*}
  (stack : Edge → List G) (X : Option G → Type*) [∀ i, PseudoEMetricSpace (X i)]
  (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))
  (base_metric : ∀ e side s t, edist (base e side s) (base e side t) =
    edist (base e false s) (base e false t))
  (gap_metric : ∀ e g h side s t, edist (gap e g h side s) (gap e g h side t) =
    edist (base e false s) (base e false t))

include base_metric gap_metric in
theorem bankStackLeftCurve_metric (slot : BankStackSlot stack) (s t : Parameter slot.1) :
    edist (bankStackLeftCurve stack X base gap slot s)
      (bankStackLeftCurve stack X base gap slot t) =
      edist (base slot.1 false s) (base slot.1 false t) := by
  let P (q : Σ i, Parameter slot.1 → X i) :=
    edist (q.2 s) (q.2 t) = edist (base slot.1 false s) (base slot.1 false t)
  change P (bankStackLeftData stack X base gap slot)
  unfold bankStackLeftData
  split
  · exact base_metric _ _ _ _
  · exact gap_metric _ _ _ _ _ _

include base_metric gap_metric in
theorem bankStackRightCurve_metric (slot : BankStackSlot stack) (s t : Parameter slot.1) :
    edist (bankStackRightCurve stack X base gap slot s)
      (bankStackRightCurve stack X base gap slot t) =
      edist (base slot.1 false s) (base slot.1 false t) := by
  let P (q : Σ i, Parameter slot.1 → X i) :=
    edist (q.2 s) (q.2 t) = edist (base slot.1 false s) (base slot.1 false t)
  change P (bankStackRightData stack X base gap slot)
  unfold bankStackRightData
  split
  · exact gap_metric _ _ _ _ _ _
  · exact base_metric _ _ _ _

include base_metric gap_metric in
/-- Consecutive actual bank curves are equally paced on their whole shared domain. -/
theorem bankStackCurves_same_metric (slot : BankStackSlot stack) (s t : Parameter slot.1) :
    edist (bankStackLeftCurve stack X base gap slot s)
      (bankStackLeftCurve stack X base gap slot t) =
    edist (bankStackRightCurve stack X base gap slot s)
      (bankStackRightCurve stack X base gap slot t) :=
  (bankStackLeftCurve_metric stack X base gap base_metric gap_metric slot s t).trans
    (bankStackRightCurve_metric stack X base gap base_metric gap_metric slot s t).symm

end Unfoldings.MetricGluing
