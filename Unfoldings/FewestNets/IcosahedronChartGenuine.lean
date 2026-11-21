module

public import Unfoldings.FewestNets.IcosahedronRoofChart

/-! Both the reference chart axes and the realized side normals are genuine. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.MeshStar

open NormedSpace

private theorem direction_upward_of_site {n : ℕ} (M : MeshStar (n + 1))
    (up : M.site 2 = faceHeight) : 0 < M.direction 2 := by
  have h : 0 < faceHeight := by unfold faceHeight faceHeightSq; positivity
  have site : M.site ≠ 0 := by
    intro zero
    have bad := congrArg (fun z : Space => z 2) zero
    rw [up, PiLp.zero_apply] at bad
    exact h.ne' bad
  change 0 < ‖M.site‖⁻¹ * M.site 2
  rw [up]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr site)) h

theorem face_tangent_firstAxis_ne_zero (q i j : ℕ) :
    bisectorTangent (face q i j).direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0 :=
  tangent_firstAxis_ne_zero (direction_upward_of_site (face q i j) (by
    simp [face, cornerA, cornerB, cornerC, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply]))

theorem seam_tangent_firstAxis_ne_zero (q i : ℕ) :
    bisectorTangent (seam q i).direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0 :=
  tangent_firstAxis_ne_zero (direction_upward_of_site (seam q i) (by
    simp [seam, stepU, cornerA, cornerB, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply]))

theorem pentagon_tangent_firstAxis_ne_zero (q : ℕ) :
    bisectorTangent (pentagon q).direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0 :=
  tangent_firstAxis_ne_zero (direction_upward_of_site (pentagon q) rfl)

end Unfoldings.FewestNets.MeshStar

namespace Unfoldings.FewestNets.Icosahedron.MeshStarRealization

open MeshStar

variable {q n : ℕ} {a : meshSites q} {M : MeshStar (n + 1)}
  (R : MeshStarRealization a M)

include R in
/-- A neighbor is neither its center nor its antipode because both distinct
corners belong to an outward chord triangle. -/
theorem bisectorTangent_neighbor_ne_zero (hq : 0 < q) (i : Fin (n + 1)) :
    bisectorTangent M.direction (M.neighborDirection i) ≠ 0 := by
  intro zero
  let s := M.direction
  let t := M.neighborDirection i
  let d := inner ℝ s t
  have parallel : t = d • s := sub_eq_zero.mp zero
  have ratio : |d| = 1 := by
    have h : ‖t‖ = 1 := R.neighborDirection_unit hq i
    rw [parallel, norm_smul, Real.norm_eq_abs, R.direction_unit hq, mul_one] at h
    exact h
  have center : inscribedCorners (R.face i) (R.index i 0) = (a : Space) :=
    (R.corner_eq i 0).trans R.center
  have neighbor : inscribedCorners (R.face i) (R.index i 1) = R.frame t := R.corner_eq i 1
  have corner_ne : inscribedCorners (R.face i) (R.index i 0) ≠
      inscribedCorners (R.face i) (R.index i 1) := by
    intro same
    exact (R.index i).injective.ne (by decide : (0 : Fin 3) ≠ 1)
      (siteOfCorner_injective hq (R.face i) (Subtype.ext same))
  rcases (abs_eq (zero_le_one : (0 : ℝ) ≤ 1)).mp ratio with hc | hc
  · have eq : t = s := by rw [parallel, hc, one_smul]
    apply corner_ne
    rw [center, neighbor, eq]
    exact R.center.symm
  · have eq : t = -s := by rw [parallel, hc, neg_one_smul]
    have bad : inscribedCorners (R.face i) (R.index i 1) = -(a : Space) := by
      rw [neighbor, eq, map_neg]
      exact congrArg Neg.neg R.center
    have first := inner_facetNormal_corner_pos hq (R.face i) (R.index i 0)
    have last := inner_facetNormal_corner_pos hq (R.face i) (R.index i 1)
    rw [center] at first
    rw [bad, inner_neg_right] at last
    linarith only [first, last]

end Unfoldings.FewestNets.Icosahedron.MeshStarRealization
