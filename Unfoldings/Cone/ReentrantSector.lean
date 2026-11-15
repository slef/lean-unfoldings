module

public import Unfoldings.Cone.AngularRegion

/-! Actual geometric sectors with any width strictly between zero and a full turn. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s u : Set E}

/-- Renaming an equal geometric region preserves its constructed intrinsic metric. -/
def congrIsometryEquiv (same : s = u) : PolygonalPoint s ≃ᵢ PolygonalPoint u := by
  subst u
  exact IsometryEquiv.refl _

@[simp] theorem congrIsometryEquiv_val (same : s = u) (x : PolygonalPoint s) :
    (congrIsometryEquiv same x).val = x.val := by
  subst u
  rfl

end Unfoldings.PolygonalPoint

namespace Unfoldings

/-- A geometric sector retains its whole real heading interval, including reentrant angles.
Its metric below is the intrinsic polygonal metric of this actual subset of the plane. -/
def closedAngularSector (width : ℝ) : Set ℂ :=
  {z | ∃ r : ℝ≥0, ∃ θ ∈ Set.Icc 0 width, z = (r : ℂ) * polarRay θ}

namespace AngularFan

variable {n : ℕ} (A : AngularFan n)

/-- This identifies the actual region even for fans wider than a half-turn. -/
theorem planarRegion_eq_closedAngularSector :
    A.planarRegion = closedAngularSector A.totalAngle := by
  ext z
  constructor
  · intro member
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
    obtain ⟨r, θ, bounds, equal⟩ := (A.mem_faceImage_iff i z).mp hi
    exact ⟨r, θ, ⟨(A.heading_nonneg _).trans bounds.1,
      bounds.2.trans (A.heading_le_totalAngle _)⟩, equal⟩
  · rintro ⟨r, θ, bounds, equal⟩
    obtain ⟨i, interval⟩ := A.exists_closed_heading_piece θ bounds
    exact Set.mem_iUnion.mpr ⟨i, (A.mem_faceImage_iff i z).mpr ⟨r, θ, interval, equal⟩⟩

/-- The whole slit fan is the intrinsic geometric sector, allowing reentrant angles. -/
def intrinsicAngularSectorIsometryEquiv (small : A.totalAngle < 2 * Real.pi) :
    A.Surface ≃ᵢ PolygonalPoint (closedAngularSector A.totalAngle) :=
  (A.intrinsicRegionIsometryEquiv small).trans
    (PolygonalPoint.congrIsometryEquiv A.planarRegion_eq_closedAngularSector)

@[simp] theorem intrinsicAngularSectorIsometryEquiv_val (small : A.totalAngle < 2 * Real.pi)
    (x : A.Surface) : (A.intrinsicAngularSectorIsometryEquiv small x).val = A.develop x := by
  simp only [intrinsicAngularSectorIsometryEquiv, IsometryEquiv.trans_apply,
    PolygonalPoint.congrIsometryEquiv_val, intrinsicRegionIsometryEquiv_val]

end AngularFan

/-- Two genuine convex halves construct every positive geometric sector below a full turn. -/
def bisectedSectorFan (width : ℝ) (positive : 0 < width) (small : width < 2 * Real.pi) :
    AngularFan 1 where
  angle _ := width / 2
  positive _ := half_pos positive
  small _ := by linarith

@[simp] theorem bisectedSectorFan_totalAngle (width : ℝ) (positive : 0 < width)
    (small : width < 2 * Real.pi) :
    (bisectedSectorFan width positive small).totalAngle = width := by
  change (∑ _ : Fin 2, width / 2) = width
  rw [Fin.sum_univ_two]
  ring

/-- Reentrant sectors have a constructed two-cell intrinsic model, with physical placement
unchanged. No Euclidean chord-distance assertion is made across the missing wedge. -/
def reentrantSectorIsometryEquiv (width : ℝ) (positive : 0 < width)
    (small : width < 2 * Real.pi) :
    (bisectedSectorFan width positive small).Surface ≃ᵢ
      PolygonalPoint (closedAngularSector width) :=
  ((bisectedSectorFan width positive small).intrinsicAngularSectorIsometryEquiv
    (by rwa [bisectedSectorFan_totalAngle])).trans
      (PolygonalPoint.congrIsometryEquiv (by rw [bisectedSectorFan_totalAngle]))

@[simp] theorem reentrantSectorIsometryEquiv_val (width : ℝ) (positive : 0 < width)
    (small : width < 2 * Real.pi) (x : (bisectedSectorFan width positive small).Surface) :
    (reentrantSectorIsometryEquiv width positive small x).val =
      (bisectedSectorFan width positive small).develop x := by
  simp only [reentrantSectorIsometryEquiv, IsometryEquiv.trans_apply,
    PolygonalPoint.congrIsometryEquiv_val, AngularFan.intrinsicAngularSectorIsometryEquiv_val]

end Unfoldings
