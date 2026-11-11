module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Height graphs of coordinate-monotone planar boundaries, closed under lattice operations. -/

@[expose] public section

namespace Unfoldings

/-- At diagonal height `h = x + y`, both coordinates of this graph increase.
The two order conditions imply continuity; it is not an additional assumption. -/
structure MonotoneHeightGraph where
  coordinate : ℝ → ℝ
  coordinate_mono : Monotone coordinate
  complement_mono : Monotone (fun h => h - coordinate h)

namespace MonotoneHeightGraph

variable (G H : MonotoneHeightGraph)

theorem coordinate_sub_le {a b : ℝ} (ordered : a ≤ b) :
    G.coordinate b - G.coordinate a ≤ b - a := by
  have bound := G.complement_mono ordered
  linarith

theorem lipschitz : LipschitzWith 1 G.coordinate := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rcases le_total a b with ordered | ordered
  · rw [abs_of_nonpos (sub_nonpos.mpr (G.coordinate_mono ordered)),
      abs_of_nonpos (sub_nonpos.mpr ordered)]
    linarith [G.coordinate_sub_le ordered]
  · rw [abs_of_nonneg (sub_nonneg.mpr (G.coordinate_mono ordered)),
      abs_of_nonneg (sub_nonneg.mpr ordered)]
    exact G.coordinate_sub_le ordered

theorem continuous : Continuous G.coordinate := G.lipschitz.continuous

/-- The right envelope of two monotone boundaries remains coordinate-monotone. -/
def max : MonotoneHeightGraph where
  coordinate h := Max.max (G.coordinate h) (H.coordinate h)
  coordinate_mono _ _ ordered := max_le_max (G.coordinate_mono ordered)
    (H.coordinate_mono ordered)
  complement_mono := by
    intro a b ordered
    change a - Max.max (G.coordinate a) (H.coordinate a) ≤
      b - Max.max (G.coordinate b) (H.coordinate b)
    rw [← min_sub_sub_left, ← min_sub_sub_left]
    exact min_le_min (G.complement_mono ordered) (H.complement_mono ordered)

/-- The left envelope of two monotone boundaries remains coordinate-monotone. -/
def min : MonotoneHeightGraph where
  coordinate h := Min.min (G.coordinate h) (H.coordinate h)
  coordinate_mono _ _ ordered := min_le_min (G.coordinate_mono ordered)
    (H.coordinate_mono ordered)
  complement_mono := by
    intro a b ordered
    change a - Min.min (G.coordinate a) (H.coordinate a) ≤
      b - Min.min (G.coordinate b) (H.coordinate b)
    rw [← max_sub_sub_left, ← max_sub_sub_left]
    exact max_le_max (G.complement_mono ordered) (H.complement_mono ordered)

/-- Clamping a monotone connector between monotone boundaries preserves both coordinates. -/
def clamp (connector : MonotoneHeightGraph) : MonotoneHeightGraph :=
  G.max (H.min connector)

theorem clamp_mem (connector : MonotoneHeightGraph)
    (ordered : ∀ h, G.coordinate h ≤ H.coordinate h) (h : ℝ) :
    G.coordinate h ≤ (G.clamp H connector).coordinate h ∧
      (G.clamp H connector).coordinate h ≤ H.coordinate h := by
  exact ⟨le_max_left _ _, max_le (ordered h) (min_le_left _ _)⟩

theorem clamp_eq (connector : MonotoneHeightGraph) {h : ℝ}
    (first : G.coordinate h ≤ connector.coordinate h)
    (last : connector.coordinate h ≤ H.coordinate h) :
    (G.clamp H connector).coordinate h = connector.coordinate h := by
  exact (congrArg (Max.max (G.coordinate h)) (min_eq_right last)).trans (max_eq_right first)

def point (h : ℝ) : ℂ := ⟨G.coordinate h, h - G.coordinate h⟩

@[simp] theorem point_height (h : ℝ) : (G.point h).re + (G.point h).im = h := by
  change G.coordinate h + (h - G.coordinate h) = h
  ring

theorem point_injective : Function.Injective G.point := by
  intro a b same
  simpa only [G.point_height] using congrArg (fun z : ℂ => z.re + z.im) same

theorem point_continuous : Continuous G.point := by
  have parts := (Complex.continuous_ofReal.comp G.continuous).add
    ((Complex.continuous_ofReal.comp (continuous_id.sub G.continuous)).mul
      (continuous_const (y := Complex.I)))
  convert parts using 1
  ext h
  apply Complex.ext <;> simp [point]

end MonotoneHeightGraph
end Unfoldings
