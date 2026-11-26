module

public import Unfoldings.FewestNets.LatitudeRingsChordPairing
public import Unfoldings.FewestNets.LatitudeRingsNorthSector
public import Mathlib.Analysis.Normed.Module.Normalize

/-! The actual paired chord triangles cover the sphere with disjoint strict interiors. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.LatitudeRings

open Real Module
open scoped Topology

variable {G : LatitudeRings} (hG : Oriented G)

local notation "North" => latitudeSite 0 0
local notation "Sphere" => Subtype (fun p : Space => p ∈ Metric.sphere (0 : Space) 1)
local notation "B" => chordBasis hG

include hG in
private theorem firstNorthSector_ray (ε : ℝ) (pos : 0 < ε) :
    let d := longitudeStep G 0
    let t := d / 2
    let p := North + ε • (rowSite G 0 1 + rowSite G 0 0)
    meridianTransverse t p = 0 ∧ 0 < meridianCoordinate t p := by
  let d := longitudeStep G 0
  let t := d / 2
  let p := North + ε • (rowSite G 0 1 + rowSite G 0 0)
  change meridianTransverse t p = 0 ∧ 0 < meridianCoordinate t p
  have d_bounds := longitudeStep_pos_lt_pi hG.toAdmissible (Nat.zero_le (stripCount G))
  have row := colatitude_mem hG.toAdmissible (Nat.zero_le (stripCount G))
  have sine := sin_pos_of_pos_of_lt_pi row.1 row.2
  have cosine : 0 < cos t := cos_pos_of_mem_Ioo
    ⟨by dsimp only [t, d]; linarith only [d_bounds.1, pi_pos],
     by dsimp only [t, d]; linarith only [d_bounds.2]⟩
  have longitude₀ : rowLongitude (rowSize G 0) 0 = 0 := by simp [rowLongitude]
  have longitude₁ : rowLongitude (rowSize G 0) 1 = d := by
    unfold rowLongitude d longitudeStep
    push_cast
    ring
  have two : d - t = t := by dsimp only [t]; ring
  constructor
  · simp [p, rowSite, longitude₀, longitude₁, two, sin_neg]
  · simp only [p, map_add, map_smul, smul_eq_mul, rowSite, longitude₀, longitude₁,
      meridianCoordinate_latitudeSite, sin_zero, zero_mul, zero_add, two, zero_sub, cos_neg]
    exact mul_pos pos (add_pos (mul_pos sine cosine) (mul_pos sine cosine))

private theorem exists_chord_weight_two :
    ∃ p : Sphere, (∀ i j, p.val ≠ B i j) ∧
      (∑ i, radialTriangleWeight (B i) p.val) = 2 := by
  classical
  let : NeZero (rowSize G 0) := ⟨(rowSize_pos hG.toAdmissible (Nat.zero_le _)).ne'⟩
  let first : ChordFace G := .inl 0
  let branch := rowSite G 0 1 + rowSite G 0 0
  obtain ⟨r, r_pos, ball⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_northPole_outside_elsewhere hG.toAdmissible B (chordBasis_apply hG))
  let ε := r / (‖branch‖ + 1)
  have ε_pos : 0 < ε := div_pos r_pos (by positivity)
  let q := North + ε • branch
  have in_ball : q ∈ Metric.ball North r := by
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖North + ε • branch - North‖ < r
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ε_pos]
    change ε * ‖branch‖ < r
    have scaled : ε * (‖branch‖ + 1) = r := div_mul_cancel₀ r (by positivity)
    linarith only [scaled, ε_pos]
  have axis := firstNorthSector_ray hG ε ε_pos
  have q_ne : q ≠ 0 := by
    intro zero
    have forward : 0 < meridianCoordinate (longitudeStep G 0 / 2) q := axis.2
    rw [zero, map_zero] at forward
    exact (lt_irrefl _ forward)
  let p := NormedSpace.normalize q
  have scale : 0 < ‖q‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr q_ne)
  have strict (j : Fin 3) : 0 < (B first).coord j p := by
    have first_site : B first 0 = North := chordBasis_apply hG first 0
    have second_site : B first 1 = rowSite G 0 1 := chordBasis_apply hG first 1
    have third_site : B first 2 = rowSite G 0 0 := chordBasis_apply hG first 2
    have expansion : q = B first 0 + ε • (B first 1 + B first 2) := by
      rw [first_site, second_site, third_site]
    change 0 < (B first).coord j (‖q‖⁻¹ • q)
    rw [map_smul, smul_eq_mul]
    apply mul_pos scale
    rw [expansion, map_add, map_smul, map_add, smul_eq_mul]
    simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    fin_cases j <;> norm_num [ε_pos]
  have absent (i : ChordFace G) (different : i ≠ first) :
      ¬ ∀ j, 0 ≤ (B i).coord j p := by
    intro nonneg
    have weak (j : Fin 3) : 0 ≤ (B i).coord j q := by
      have h := nonneg j
      change 0 ≤ (B i).coord j (‖q‖⁻¹ • q) at h
      rw [map_smul, smul_eq_mul] at h
      exact nonneg_of_mul_nonneg_right h scale
    rcases i with e | e
    · have later : 0 < e.val := by
        by_contra! impossible
        exact different (congrArg Sum.inl (Fin.ext (Nat.eq_zero_of_le_zero impossible)))
      exact northSectorFirst_only hG.toAdmissible e later (B _) (chordBasis_apply hG _)
        q axis.1 axis.2 weak
    · exact ball q in_ball e weak
  let point : Sphere := ⟨p, Metric.mem_sphere.mpr
    ((dist_zero_right _).trans (NormedSpace.norm_normalize q_ne))⟩
  refine ⟨point, ?_, ?_⟩
  · intro i j equal
    change p = B i j at equal
    by_cases same : i = first
    · subst i
      obtain ⟨k, diff⟩ := exists_ne j
      have impossible := strict k
      rw [equal, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply,
        ite_eq_right diff.symm] at impossible
      exact (lt_irrefl _ impossible)
    · apply absent i same
      intro k
      rw [equal, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
      split <;> norm_num
  · have exactly : radialTriangleWeight (B first) p = 2 := by simp only [radialTriangleWeight, ite_eq_left strict]
    have zero (i : ChordFace G) (different : i ≠ first) : radialTriangleWeight (B i) p = 0 := by
      have weak := absent i different
      have not_strict : ¬ ∀ j, 0 < (B i).coord j p := fun h => weak (fun j => (h j).le)
      simp only [radialTriangleWeight, ite_eq_right not_strict, ite_eq_right weak]
    change (∑ i, radialTriangleWeight (B i) p) = 2
    rw [Finset.sum_eq_single first (fun i _ different => zero i different) (by simp), exactly]

/-- The revised latitude sweep and both fans give a spherical partition. -/
theorem chordSphere_partition :
    (⋃ i, chordTriangleOnSphere (B i)) = Set.univ ∧
      Pairwise fun i j => Disjoint (strictChordTriangleOnSphere (B i))
        (strictChordTriangleOnSphere (B j)) := by
  obtain ⟨p, regular, weight⟩ := exists_chord_weight_two hG
  let : Nonempty (ChordFace G) := ⟨.inl ⟨0, rowSize_pos hG.toAdmissible (Nat.zero_le _)⟩⟩
  exact chordTriangle_partition_of_weight_two B
    (by intro i j; rw [chordBasis_apply]; exact chordVertices_unit G i j)
    (chordSideMate G) (chordSideMate_involutive G)
    (fun e => (chordBasis_edge_pair hG e).1)
    (fun e => (chordBasis_edge_pair hG e).2) p regular weight

end Unfoldings.FewestNets.LatitudeRings
