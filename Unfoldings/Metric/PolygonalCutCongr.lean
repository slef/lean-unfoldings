module

public import Unfoldings.Metric.PolygonalCut

/-! Replacing a presentation by the same literal physical cells preserves cut copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {E I : Type*} [NormedAddCommGroup E] [Finite I]
  {cells other : I → Set E} (closed : ∀ i, IsClosed (cells i))
  (other_closed : ∀ i, IsClosed (other i)) (same : cells = other) (cuts : Set E)

/-- Equality of the literal physical cells gives equality of their complete cut metrics. -/
def polygonalCutCongr : PolygonalCut cells closed cuts ≃ᵢ PolygonalCut other other_closed cuts := by
  cases same
  exact IsometryEquiv.refl _

@[simp] theorem polygonalCutCongr_of (i : I) (x : cells i) :
    polygonalCutCongr closed other_closed same cuts
      (of (fun i => cells i) (cutSeams cells closed cuts).relation i x) =
        of (fun i => other i) (cutSeams other other_closed cuts).relation i
          ⟨x.val, Eq.mp (congrArg (fun a : I → Set E => x.val ∈ a i) same) x.property⟩ := by
  cases same
  rfl

@[simp] theorem polygonalCutCongr_symm_of (i : I) (x : other i) :
    (polygonalCutCongr closed other_closed same cuts).symm
      (of (fun i => other i) (cutSeams other other_closed cuts).relation i x) =
        of (fun i => cells i) (cutSeams cells closed cuts).relation i
          ⟨x.val, Eq.mpr (congrArg (fun a : I → Set E => x.val ∈ a i) same) x.property⟩ := by
  cases same
  rfl

/-- Rewriting the cell presentation retains the original spatial fold point. -/
theorem fold_polygonalCutCongr (x : PolygonalCut cells closed cuts) :
    (cutSeams other other_closed cuts).fold (polygonalCutCongr closed other_closed same cuts x) =
      (cutSeams cells closed cuts).fold x := by
  cases same
  rfl

theorem fold_polygonalCutCongr_symm (x : PolygonalCut other other_closed cuts) :
    (cutSeams cells closed cuts).fold
      ((polygonalCutCongr closed other_closed same cuts).symm x) =
        (cutSeams other other_closed cuts).fold x := by
  cases same
  rfl

end Unfoldings.MetricGluing
