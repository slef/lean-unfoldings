module

public import Unfoldings.Geometry.MonotoneStripTopology
public import Unfoldings.Geometry.SubdivisionWallContacts

/-! Ordered locally affine banks cannot have an approached zero-width pinch. -/

@[expose] public section

namespace Unfoldings

open Filter Topology

namespace MonotoneHeightGraph

def AffineAt (G : MonotoneHeightGraph) (h : ℝ) : Prop :=
  ∃ a b : ℝ, ∀ᶠ k in 𝓝 h, G.coordinate k = a + b * k

theorem AffineAt.congr {G H : MonotoneHeightGraph} {h : ℝ} (first : G.AffineAt h)
    (equal : ∀ᶠ k in 𝓝 h, H.coordinate k = G.coordinate k) : H.AffineAt h := by
  obtain ⟨a, b, affine⟩ := first
  exact ⟨a, b, equal.and affine |>.mono (fun _ member => member.1.trans member.2)⟩

theorem AffineAt.congr_on_Ioo {G H : MonotoneHeightGraph} {a b h : ℝ}
    (first : G.AffineAt h) (equal : Set.EqOn H.coordinate G.coordinate (Set.Ioo a b))
    (inside : h ∈ Set.Ioo a b) : H.AffineAt h :=
  first.congr (Filter.mem_of_superset (isOpen_Ioo.mem_nhds inside) equal)

theorem affine_affineAt (height x slope : ℝ) (nonnegative : 0 ≤ slope) (small : slope ≤ 1)
    (h : ℝ) : (affine height x slope nonnegative small).AffineAt h := by
  refine ⟨x - slope * height, slope, Filter.Eventually.of_forall (fun k => ?_)⟩
  change x + slope * (k - height) = _
  ring

theorem locally_eq_of_ordered_affine_contact {G H : MonotoneHeightGraph} {h : ℝ}
    (first : G.AffineAt h) (last : H.AffineAt h)
    (ordered : ∀ k, G.coordinate k ≤ H.coordinate k)
    (same : G.coordinate h = H.coordinate h) :
    ∀ᶠ k in 𝓝 h, G.coordinate k = H.coordinate k := by
  obtain ⟨a, b, first⟩ := first
  obtain ⟨c, d, last⟩ := last
  have at_base : a + b * h = c + d * h :=
    (first.self_of_nhds).symm.trans (same.trans last.self_of_nhds)
  obtain ⟨δ, positive, near⟩ := Metric.eventually_nhds_iff.mp (first.and last)
  have before := near (show dist (h - δ / 2) h < δ by
    rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos (by positivity)]
    linarith)
  have after := near (show dist (h + δ / 2) h < δ by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity)]
    linarith)
  have lower := ordered (h - δ / 2)
  have upper := ordered (h + δ / 2)
  rw [before.1, before.2] at lower
  rw [after.1, after.2] at upper
  have product : (b - d) * δ = 0 := by nlinarith
  have coefficients : b = d := sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_right positive.ne')
  have constants : a = c := by rw [coefficients] at at_base; linarith
  filter_upwards [first, last] with k first last
  rw [first, last, coefficients, constants]

end MonotoneHeightGraph

namespace MonotoneStrip

variable (S : MonotoneStrip)

theorem not_mem_closure_strictCarrier_of_affine_pinch {h : ℝ}
    (first : S.lower.AffineAt h) (last : S.upper.AffineAt h)
    (same : S.lower.coordinate h = S.upper.coordinate h) :
    S.lower.point h ∉ closure S.strictCarrier := by
  intro approached
  have equal := MonotoneHeightGraph.locally_eq_of_ordered_affine_contact first last S.ordered same
  have continuous : Continuous (fun z : ℂ => z.re + z.im) :=
    Complex.continuous_re.add Complex.continuous_im
  have height := continuous.continuousAt (x := S.lower.point h)
  change Tendsto _ _ (𝓝 ((S.lower.point h).re + (S.lower.point h).im)) at height
  rw [S.lower.point_height] at height
  obtain ⟨z, collapsed, strict⟩ := mem_closure_iff_nhds.mp approached _ (height.eventually equal)
  exact (strict.1.trans strict.2).ne collapsed

/-- This records terminal pinches too, unlike the reopening-pinch invariant. -/
def ApproachedPinchesIn (V : Set ℂ) (a b : ℝ) : Prop :=
  ∀ h ∈ Set.Ioo a b, S.lower.coordinate h = S.upper.coordinate h →
    S.lower.point h ∈ closure S.strictCarrier → S.lower.point h ∈ V

theorem approachedPinchesIn_of_positive_width (V : Set ℂ) (a b : ℝ)
    (width : ∀ h ∈ Set.Ioo a b, S.lower.coordinate h < S.upper.coordinate h) :
    S.ApproachedPinchesIn V a b := by
  intro h member same
  exact ((width h member).ne same).elim

end MonotoneStrip
end Unfoldings
