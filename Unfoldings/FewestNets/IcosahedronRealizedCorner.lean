module

public import Unfoldings.FewestNets.IcosahedronRealizedStar
public import Unfoldings.FewestNets.IcosahedronVertexGuard
public import Unfoldings.FewestNets.MeshCornerTransport

/-! Transfer exact model corner inequalities to the actual Voronoi network. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry Real

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

private theorem facetNormal_angle_adjacent_pos {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t : MeshFace q) (j : Fin 3) :
    0 < angle (facetNormal hq t) (facetNormal hq (adjacentFace hq t j)) := by
  have ne := (facetNormal_injective qbig hq).ne (adjacentFace_ne qbig hq t j).symm
  apply lt_of_le_of_ne (angle_nonneg _ _)
  intro hz
  have h := inner_eq_mul_norm_of_angle_eq_zero hz.symm
  rw [facetNormal_unit, facetNormal_unit, mul_one] at h
  exact (inner_lt_one_iff_real_of_norm_eq_one (facetNormal_unit hq t)
    (facetNormal_unit hq _)).mpr ne |>.ne h

private theorem facetNormal_inner_adjacent_pos {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t : MeshFace q) (j : Fin 3) :
    0 < inner ℝ (facetNormal hq t) (facetNormal hq (adjacentFace hq t j)) := by
  rw [inner_eq_cos_angle_of_norm_eq_one (facetNormal_unit hq t) (facetNormal_unit hq _)]
  have nonnegative := angle_nonneg (facetNormal hq t) (facetNormal hq (adjacentFace hq t j))
  exact cos_pos_of_mem_Ioo ⟨by linarith only [nonnegative, pi_pos],
    facetNormal_angle_adjacent_lt qbig hq t j⟩

private theorem meshGnomonic_ne_zero_of_short {u v : Space} (uu : ‖u‖ = 1) (vu : ‖v‖ = 1)
    (positive : 0 < angle u v) (short : angle u v < π / 2) : meshGnomonic u v ≠ 0 := by
  have upper : angle u v < π := short.trans (by linarith [pi_pos])
  have tangent_unit := (closedMinorArc_arclength uu vu positive upper).1
  have factor : 0 < sin (angle u v) / cos (angle u v) :=
    div_pos (sin_pos_of_pos_of_lt_pi positive upper)
      (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], short⟩)
  rw [meshGnomonic_eq_smul_minorArcTangent uu vu positive short]
  exact smul_ne_zero factor.ne' (norm_ne_zero_iff.mp (tangent_unit.trans_ne one_ne_zero))

namespace MeshStarRealization

variable {q n : ℕ} {a : meshSites q} {star : MeshStar (n + 1)}
  (R : MeshStarRealization a star)

theorem cornerAltitude_and_angle_of_model (qbig : 100 ≤ q) (hq : 0 < q)
    (o : Orientation ℝ Plane (Fin 2)) (k : Fin (n + 1)) (first : k ≠ k - 1) (last : k ≠ k + 1)
    (outward : ∀ l, 0 < inner ℝ star.direction (star.dual l))
    {r ψ : ℝ} (lo : 0 ≤ ψ) (hi : ψ ≤ π)
    (altitude : tan r < meshCornerAltitude (star.cornerRay k (k - 1)) (star.cornerRay k (k + 1)))
    (cosine : meshCornerCosine (star.cornerRay k (k - 1)) (star.cornerRay k (k + 1)) < cos ψ) :
    tan r < cornerGuardAltitude o hq (R.face k) (R.index k 2) (R.index k 1) ∧
      ψ < angle (minorArcTangent (facetNormal hq (R.face k))
        (facetNormal hq (adjacentFace hq (R.face k) (R.index k 2))))
        (minorArcTangent (facetNormal hq (R.face k))
          (facetNormal hq (adjacentFace hq (R.face k) (R.index k 1)))) := by
  let t := R.face k
  let j := R.index k 2
  let l := R.index k 1
  let N := facetNormal hq t
  let P := facetNormal hq (adjacentFace hq t j)
  let Q := facetNormal hq (adjacentFace hq t l)
  have N_eq : N = R.frame (star.dualDirection k) := R.facetNormal_eq hq k (outward k)
  have P_eq : P = R.frame (star.dualDirection (k - 1)) := by
    dsimp only [P, t, j]
    rw [R.adjacentFace_pred qbig hq k first, R.facetNormal_eq hq _ (outward (k - 1))]
  have Q_eq : Q = R.frame (star.dualDirection (k + 1)) := by
    dsimp only [Q, t, l]
    rw [R.adjacentFace_succ qbig hq k last, R.facetNormal_eq hq _ (outward (k + 1))]
  have alt_eq : cornerGuardAltitude o hq t j l =
      meshCornerAltitude (meshGnomonic N P) (meshGnomonic N Q) :=
    centeredSlope_altitude_eq o (facetNormal_unit hq t)
      (facetNormal_inner_adjacent_pos qbig hq t j).ne'
      (facetNormal_inner_adjacent_pos qbig hq t l).ne'
  have cos_eq : meshCornerCosine (meshGnomonic N P) (meshGnomonic N Q) =
      meshCornerCosine (star.cornerRay k (k - 1)) (star.cornerRay k (k + 1)) := by
    rw [N_eq, P_eq, Q_eq, meshGnomonic_map, meshGnomonic_map, meshCornerCosine_map]
    rfl
  have shortP := facetNormal_angle_adjacent_lt qbig hq t j
  have shortQ := facetNormal_angle_adjacent_lt qbig hq t l
  have posP := facetNormal_angle_adjacent_pos qbig hq t j
  have posQ := facetNormal_angle_adjacent_pos qbig hq t l
  have nu := facetNormal_unit hq t
  have pu := facetNormal_unit hq (adjacentFace hq t j)
  have qu := facetNormal_unit hq (adjacentFace hq t l)
  change tan r < cornerGuardAltitude o hq t j l ∧ ψ < angle (minorArcTangent N P)
    (minorArcTangent N Q)
  constructor
  · rw [alt_eq, N_eq, P_eq, Q_eq, meshGnomonic_map, meshGnomonic_map, meshCornerAltitude_map]
    exact altitude
  rw [← angle_meshGnomonic_eq_incident nu pu qu posP posQ shortP shortQ]
  exact angle_gt_of_meshCornerCosine_lt (meshGnomonic_ne_zero_of_short nu pu posP shortP)
    (meshGnomonic_ne_zero_of_short nu qu posQ shortQ) lo hi (cos_eq.trans_lt cosine)

end MeshStarRealization

end Unfoldings.FewestNets.Icosahedron
