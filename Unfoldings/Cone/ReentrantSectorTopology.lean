module

public import Unfoldings.Cone.ComplementarySectors
public import Unfoldings.Cone.HeadingSector
public import Unfoldings.Geometry.ConvexCellRegion

/-! Exact closedness, regularity and geometric interiors for sectors below one full turn. -/

@[expose] public section

noncomputable section

open Filter Topology
open scoped NNReal

namespace Unfoldings

theorem isClosed_closedAngularSector (width : ℝ) (positive : 0 < width)
    (small : width < 2 * Real.pi) : IsClosed (closedAngularSector width) := by
  let A := bisectedSectorFan width positive small
  have cover := A.planarRegion_eq_closedAngularSector
  rw [bisectedSectorFan_totalAngle] at cover
  rw [← cover]
  exact isClosed_iUnion_of_finite A.isClosed_faceImage

/-- Every genuine sector is the closure of its geometric interior, including reentrant sectors. -/
theorem closure_interior_closedAngularSector (width : ℝ) (positive : 0 < width)
    (small : width < 2 * Real.pi) : closure (interior (closedAngularSector width)) =
      closedAngularSector width := by
  let A := bisectedSectorFan width positive small
  have cover := A.planarRegion_eq_closedAngularSector
  rw [bisectedSectorFan_totalAngle] at cover
  apply Set.Subset.antisymm
  · exact closure_minimal interior_subset (isClosed_closedAngularSector width positive small)
  · rw [← cover]
    intro z member
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
    have cell_full : (interior (A.faceImage i)).Nonempty := by
      change (interior ((rotation (Circle.exp (A.heading i.castSucc))).toHomeomorph ''
        planarSector (A.angle i))).Nonempty
      rw [← (rotation (Circle.exp (A.heading i.castSucc))).toHomeomorph.image_interior]
      refine Set.Nonempty.image _ ⟨(1 : ℂ) + polarRay (A.angle i), ?_⟩
      rw [interior_planarSector (A.angle i)
        (Real.sin_pos_of_pos_of_lt_pi (A.positive i) (A.small i)).ne']
      exact ⟨1, zero_lt_one, 1, zero_lt_one, by simp⟩
    have regular := ConvexCellRegion.cell_regular_closed A.faceImage i (A.isClosed_faceImage i)
      (A.convex_faceImage i) cell_full
    have included : A.faceImage i ⊆ A.planarRegion := Set.subset_iUnion _ i
    have inside_closure : z ∈ closure (interior (A.faceImage i)) := by rwa [regular]
    exact closure_mono (interior_mono included) inside_closure

/-- Any strict positive-radius heading has a small genuine convex wedge inside the whole sector. -/
theorem polar_mem_interior_closedAngularSector (width r θ : ℝ) (positive : 0 < r)
    (heading : θ ∈ Set.Ioo 0 width) :
    (r : ℂ) * polarRay θ ∈ interior (closedAngularSector width) := by
  let δ := min (min (θ / 2) ((width - θ) / 2)) (Real.pi / 4)
  have δpos : 0 < δ := lt_min (lt_min (half_pos heading.1)
    (half_pos (sub_pos.mpr heading.2))) (div_pos Real.pi_pos (by norm_num))
  have first : δ ≤ θ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have last : δ ≤ (width - θ) / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have short : δ ≤ Real.pi / 4 := min_le_right _ _
  let a := θ - δ
  let b := θ + δ
  have gap : 0 < b - a := by dsimp [a, b]; linarith
  have small : b - a < Real.pi := by dsimp [a, b]; linarith [Real.pi_pos]
  have included : headingSector a b ⊆ closedAngularSector width := by
    intro z hz
    obtain ⟨s, φ, bounds, equal⟩ := (mem_headingSector_iff_polar a b gap small z).mp hz
    exact ⟨s, φ, ⟨by dsimp [a] at bounds; linarith [bounds.1],
      by dsimp [b] at bounds; linarith [bounds.2]⟩, equal⟩
  apply interior_mono included
  change (r : ℂ) * polarRay θ ∈ interior
    ((rotation (Circle.exp a)).toHomeomorph '' planarSector (b - a))
  rw [← (rotation (Circle.exp a)).toHomeomorph.image_interior]
  refine ⟨(r : ℂ) * polarRay (θ - a),
    polar_mem_interior_planarSector (b - a) r (θ - a) gap small positive
      ⟨by dsimp [a]; linarith, by dsimp [a, b]; linarith⟩, ?_⟩
  have placed := rotate_polar_point a (θ - a) (⟨r, positive.le⟩ : ℝ≥0)
  rw [add_sub_cancel] at placed
  exact placed

end Unfoldings
