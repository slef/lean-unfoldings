module

public import Unfoldings.Geometry.RadialCornerSector
public import Unfoldings.Geometry.ChainAffineMap

/-! Reflection exchanges the oriented banks while preserving their positive geometric aperture. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Reflect the actual unit ray, with its real heading negated. -/
theorem conj_polarRay (θ : ℝ) : starRingEnd ℂ (polarRay θ) = polarRay (-θ) := by
  apply Complex.ext <;> simp

/-- Reflection and exchange of the two original banks preserve the positive aperture,
including reentrant angles and coincident bank directions. -/
theorem positiveGapAngle_conj_reverse (d e : ℂ) (first : d ≠ 0) (last : e ≠ 0) :
    positiveGapAngle (starRingEnd ℂ e) (starRingEnd ℂ d) = positiveGapAngle d e := by
  have normalized (z : ℂ) : starRingEnd ℂ z / (‖z‖ : ℂ) =
      starRingEnd ℂ (z / (‖z‖ : ℂ)) := by
    rw [map_div₀, Complex.conj_ofReal]
  unfold positiveGapAngle initialGapAngle
  rw [Complex.norm_conj, Complex.norm_conj, normalized, normalized,
    ← polarRay_arg_eq_normalized e last, ← polarRay_arg_eq_normalized d first,
    conj_polarRay, conj_polarRay, polarRay_div, polarRay_div]
  have same : -d.arg - -e.arg = e.arg - d.arg := by ring
  rw [same]

namespace PolygonalChain

variable {n : ℕ} (P : PolygonalChain ℂ n)

/-- Reflect all actual original vertices, retaining their order and edge labels. -/
def conjugate : PolygonalChain ℂ n :=
  P.affineMap Complex.conjLIE.toLinearIsometry.toAffineMap

@[simp] theorem conjugate_vertex (i : Fin (n + 1)) :
    P.conjugate.vertex i = starRingEnd ℂ (P.vertex i) := rfl

@[simp] theorem conjugate_edge (i : Fin n) :
    P.conjugate.edge i = starRingEnd ℂ (P.edge i) := by
  simp only [edge, conjugate_vertex, map_sub]

/-- A reflected actual bend uses the complementary bank ordering. -/
theorem conjugate_left_aperture {m : ℕ} (Q : PolygonalChain ℂ (m + 1)) (k : Fin m)
    (first : Q.edge k.castSucc ≠ 0) (last : Q.edge k.succ ≠ 0) :
    positiveGapAngle (Q.conjugate.edge k.succ) (-Q.conjugate.edge k.castSucc) =
      positiveGapAngle (-Q.edge k.castSucc) (Q.edge k.succ) := by
  rw [conjugate_edge, conjugate_edge, ← map_neg]
  exact positiveGapAngle_conj_reverse _ _ (neg_ne_zero.mpr first) last

end PolygonalChain

end Unfoldings
