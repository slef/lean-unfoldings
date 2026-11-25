module

public import Unfoldings.FewestNets.ThreeExitStems

/-! An angular calibration of the disjoint-ray criterion for the actual seam choices. -/

@[expose] public section

namespace Unfoldings.ConvexRoof.ThreeExitComponentStems

open FewestNets InnerProductGeometry Real Relation

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face} {δ : ℝ}
  (R : K.ThreeExitComponentStems (slopes := slopes) seed δ)

local notation "S" => K.restrictedCarrier (K.selectionComponent slopes seed)
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ S}
local notation "p" => (fun v : V => K.projectedVertex (Subtype.val v))

private theorem displacement_ne_zero {v w : V} (up : R.choice.height v < R.choice.height w) :
    p w - p v ≠ 0 := by
  intro zero
  have equal := sub_eq_zero.mp zero
  rw [R.height_eq, R.height_eq] at up
  exact (lt_irrefl _ (equal ▸ up))

/-- Literal exit and stem heading bounds give the planar no-conflict criterion.
A side direction is used only at roots where that side is available. -/
theorem no_path_of_angular_exits (east west : Plane) (east_ne : east ≠ 0) (west_ne : west ≠ 0)
    {ε : ℝ} (ε_nonneg : 0 ≤ ε) (ε_lt : ε < δ) (δ_upper : δ ≤ π / 4)
    (east_heading : (exitHeadingChart false east).arg ∈ Set.Icc (-ε) ε)
    (west_heading : (exitHeadingChart true west).arg ∈ Set.Icc (-ε) ε)
    (east_avoids : ∀ r, R.choice.forcedEast r → ∀ t > (0 : ℝ), p r + t • east ∉ S)
    (west_avoids : ∀ r, R.choice.forcedWest r → ∀ t > (0 : ℝ), p r + t • west ∉ S)
    (separate : ∀ r s, R.choice.forcedEast r → R.choice.forcedWest s → ∀ a b : ℝ,
      0 < a → 0 < b → p r + a • east ≠ p s + b • west) :
    ∀ r s, R.choice.forcedEast r → R.choice.forcedWest s →
        ¬ ReflTransGen R.choice.constraint r s := by
  have δ_pos := ε_nonneg.trans_lt ε_lt
  have ε_upper : ε < π / 2 := by linarith only [ε_lt, δ_upper, pi_pos]
  have east_pos : 0 < east 0 :=
    threeExit_horizontal_advances false east_ne ε_upper east_heading
  have west_neg : west 0 < 0 :=
    neg_pos.mp (threeExit_horizontal_advances true west_ne ε_upper west_heading)
  refine R.choice.no_path_of_plane_rays p R.height_eq S east west east_pos west_neg
    ?_ ?_ ?_ east_avoids west_avoids ?_ ?_ separate
  · intro v w step
    rcases step with ⟨inside, parent⟩ | ⟨inside, parent⟩
    · exact parent ▸ R.east_segment v inside
    · rw [segment_symm]
      exact parent ▸ R.west_segment w inside
  · intro v inside
    exact sub_pos.mp (threeExit_stem_advances false
      (R.displacement_ne_zero (R.choice.east_up v inside)) δ_pos (R.east_heading v inside)).1
  · intro v inside
    have left := (threeExit_stem_advances true
      (R.displacement_ne_zero (R.choice.west_up v inside)) δ_pos (R.west_heading v inside)).1
    exact sub_neg.mp (neg_pos.mp left)
  · intro r _ v inside parent
    have stem_ne := R.displacement_ne_zero (R.choice.west_up v inside)
    have comparison := (threeExit_stem_below_horizontal_exit
      (show exitHeadingChart true (p (R.choice.westParent v) - p v) ≠ 0 by
        exact fun h => stem_ne ((exitHeadingChart true).map_eq_zero_iff.mp h))
      (show exitHeadingChart false east ≠ 0 by simpa using east_ne)
      ε_nonneg ε_lt (R.west_heading v inside) east_heading).2
    simpa only [parent, exitHeadingChart_re, exitHeadingChart_im, ite_true, Bool.false_eq_true, ite_false,
      PiLp.sub_apply, neg_sub] using comparison
  · intro r _ v inside parent
    have stem_ne := R.displacement_ne_zero (R.choice.east_up v inside)
    have comparison := (threeExit_stem_below_horizontal_exit
      (show exitHeadingChart false (p (R.choice.eastParent v) - p v) ≠ 0 by
        exact fun h => stem_ne ((exitHeadingChart false).map_eq_zero_iff.mp h))
      (show exitHeadingChart true west ≠ 0 by simpa using west_ne)
      ε_nonneg ε_lt (R.east_heading v inside) west_heading).2
    simpa only [parent, exitHeadingChart_re, exitHeadingChart_im, ite_true, Bool.false_eq_true, ite_false,
      PiLp.sub_apply, div_neg, neg_mul, ← mul_neg, neg_sub] using comparison

end Unfoldings.ConvexRoof.ThreeExitComponentStems
