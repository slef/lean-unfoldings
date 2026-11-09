module

public import Unfoldings.Cone.AngularInjective
public import Unfoldings.Geometry.ConvexCover

/-!
# Chords that lift across finitely many angular pieces

Below a full turn, the inverse development is well-defined on its actual
range. It is nonexpanding on every closed piece. The same bound therefore
holds on any convex set covered by the pieces, even when the whole fan has
a reentrant corner and is not a convex planar domain.
-/

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n)

theorem isClosed_faceImage (i : Fin (n + 1)) : IsClosed (A.faceImage i) :=
  (rotation (Circle.exp (A.heading i.castSucc))).toHomeomorph.isClosedMap _
    (isClosed_planarSector (A.angle i)
      (Real.sin_pos_of_pos_of_lt_pi (A.positive i) (A.small i)).ne')

/-- An inverse on the actual range, extended by the apex elsewhere. -/
def developInverse (z : ℂ) : A.Surface := by
  classical
  exact if inside : ∃ x, A.develop x = z then inside.choose else A.origin

theorem developInverse_develop (small : A.totalAngle < 2 * Real.pi) (x : A.Surface) :
    A.developInverse (A.develop x) = x := by
  have inside : ∃ y, A.develop y = A.develop x := ⟨x, rfl⟩
  rw [developInverse, dite_eq_left inside]
  exact A.develop_injective_of_lt_full small inside.choose_spec

theorem developInverse_place (small : A.totalAngle < 2 * Real.pi)
    (i : Fin (n + 1)) (x : A.Cell i) : A.developInverse (A.place i x) = A.faceMap i x :=
  A.developInverse_develop small (A.faceMap i x)

theorem developInverse_piece_lipschitz (small : A.totalAngle < 2 * Real.pi)
    (i : Fin (n + 1)) : LipschitzOnWith 1 A.developInverse (A.faceImage i) := by
  intro z hz w hw
  obtain ⟨left_point, hl, rfl⟩ := hz
  obtain ⟨right_point, hr, rfl⟩ := hw
  let x : A.Cell i := ⟨left_point, hl⟩
  let y : A.Cell i := ⟨right_point, hr⟩
  change edist (A.developInverse (A.place i x)) (A.developInverse (A.place i y)) ≤
    (1 : ℝ≥0∞) * edist (A.place i x) (A.place i y)
  rw [one_mul, A.developInverse_place small, A.developInverse_place small]
  exact ((A.faceMap_isometry i x y).trans (A.place_isometry i x y).symm).le

theorem developInverse_lipschitzOn_convex (small : A.totalAngle < 2 * Real.pi)
    (s : Set ℂ) (convex : Convex ℝ s) (cover : s ⊆ ⋃ i, A.faceImage i) :
    LipschitzOnWith 1 A.developInverse s :=
  convex_lipschitzOnWith_of_finite_closed_cover s convex A.faceImage
    A.isClosed_faceImage cover A.developInverse 1 (A.developInverse_piece_lipschitz small)

/-- Whenever the developed chord is covered, it realizes intrinsic distance,
even if the whole slit fan has angle greater than pi. -/
theorem edist_eq_of_segment_subset (small : A.totalAngle < 2 * Real.pi)
    (x y : A.Surface)
    (covered : segment ℝ (A.develop x) (A.develop y) ⊆ ⋃ i, A.faceImage i) :
    edist x y = edist (A.develop x) (A.develop y) := by
  apply le_antisymm
  · have bound := A.developInverse_lipschitzOn_convex small _ (convex_segment _ _) covered
    have endpoints := bound (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    simpa only [A.developInverse_develop small, ENNReal.coe_one, one_mul] using endpoints
  · simpa only [ENNReal.coe_one, one_mul] using A.develop_lipschitz.edist_le_mul x y

theorem dist_eq_of_segment_subset (small : A.totalAngle < 2 * Real.pi)
    (x y : A.Surface)
    (covered : segment ℝ (A.develop x) (A.develop y) ⊆ ⋃ i, A.faceImage i) :
    dist x y = dist (A.develop x) (A.develop y) := by
  have equal := congrArg ENNReal.toReal (A.edist_eq_of_segment_subset small x y covered)
  simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using equal

end Unfoldings.AngularFan
