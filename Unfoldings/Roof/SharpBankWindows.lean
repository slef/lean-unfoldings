module

public import Unfoldings.Roof.SharpOriginalBankHeading
public import Unfoldings.Geometry.PlanePolarWindow
public import Unfoldings.Polyhedron.ProjectedBoundaryChainInterval

/-! The sharp comparison controls all strict polar windows of an actual routed bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

open InnerProductGeometry

/-- Only the internal rays occur in the window sum. The original first point
may equal the radial source. -/
theorem interval_internal_angle_sum_in_frame_of_noninitial {N n : ℕ}
    (P : PolygonalChain Plane N) (L : Plane ≃ₗᵢ[ℝ] ℂ) (source : Plane)
    (genuine : ∀ i, 0 < i.val → P.vertex i - source ≠ 0)
    (first : ℕ) (fits : first + (n + 2) ≤ N) :
    (∑ k : Fin n, angle
      ((P.interval first (n + 2) fits).internalSourceRay source k.castSucc)
      ((P.interval first (n + 2) fits).internalSourceRay source k.succ)) =
      interiorVariation ((P.inComplexFrame L).polarVariation (L source))
        ⟨first, by omega⟩ ⟨first + n + 1, by omega⟩ := by
  let Q := P.inComplexFrame L
  rw [← sum_offset_eq_interiorVariation (Q.polarVariation (L source)) first fits]
  apply Finset.sum_congr rfl
  intro k _
  let a : Fin (N + 1) := ⟨first + (k.val + 1), by omega⟩
  let b : Fin (N + 1) := ⟨first + (k.val + 1 + 1), by omega⟩
  have a_ne : L (P.vertex a - source) ≠ 0 := by
    exact fun zero => genuine a (by dsimp [a]; omega)
      (L.injective (zero.trans (map_zero L).symm))
  have b_ne : L (P.vertex b - source) ≠ 0 := by
    exact fun zero => genuine b (by dsimp [b]; omega)
      (L.injective (zero.trans (map_zero L).symm))
  calc
    _ = angle (P.vertex a - source) (P.vertex b - source) := rfl
    _ = angle (L (P.vertex b - source)) (L (P.vertex a - source)) :=
      (angle_comm _ _).trans (L.toLinearIsometry.angle_map _ _).symm
    _ = |(L (P.vertex b - source) / L (P.vertex a - source)).arg| :=
      Complex.angle_eq_abs_arg b_ne a_ne
    _ = Q.polarVariation (L source) ⟨first + 1 + k.val, by omega⟩ := by
      let j : Fin N := ⟨first + 1 + k.val, by omega⟩
      have first_eq : j.castSucc = a := Fin.ext (by dsimp [j, a]; omega)
      have last_eq : j.succ = b := Fin.ext (by dsimp [j, b]; omega)
      change _ = |((L (P.vertex j.succ) - L source) /
        (L (P.vertex j.castSucc) - L source)).arg|
      rw [first_eq, last_eq, map_sub, map_sub]

end Unfoldings.PolygonalChain

namespace Unfoldings.ConvexRoof

open InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
/-- Every strict half-turn window has the same sharp heading allowance at the
actual roof tilt. This applies to any earlier contiguous history of the bank. -/
theorem abs_projectedMetricHeadingError_sub_le_sharp_of_halfturn
    {φ : ℝ} (positive : 0 < φ) (small_tilt : φ < π / 2)
    (height_bound : (3 : ℝ) / 4 ≤ cos φ) (tilt : K.TiltBound φ)
    {retain : Set C.Seam} {m : ℕ} (full : (C.boundarySystem retain).Chain m)
    (cut : ∀ i, ¬ C.IsBoundaryEdge Set.univ (C.germEdge (full.point i).val))
    (source : Plane)
    (radial : (K.folding.projectedBoundaryChain full).RadialFrom source 0)
    {γ : ℝ} (margin_pos : 0 < γ)
    (margin : let P := K.folding.projectedBoundaryChain full
      ∀ i, γ * (‖P.vertex i.castSucc - source‖ * ‖P.edge i‖) ≤
        inner ℝ (P.vertex i.castSucc - source) (P.edge i))
    (L : Plane ≃ₗᵢ[ℝ] ℂ) (i j : Fin (m + 1)) (ordered : i ≤ j)
    (short : interiorVariation
      (((K.folding.projectedBoundaryChain full).inComplexFrame L).polarVariation (L source))
        i j < π) :
    |K.projectedMetricHeadingError full i - K.projectedMetricHeadingError full j| ≤
      shallowDevelopmentHeading φ := by
  let P := K.folding.projectedBoundaryChain full
  by_cases equal : i = j
  · have cos_pos : 0 < cos φ := (by norm_num : (0 : ℝ) < 3 / 4).trans_le height_bound
    have sec := sub_nonneg.mpr (one_le_inv₀ cos_pos |>.mpr (cos_le_one φ))
    have sin_nonneg := sin_nonneg_of_nonneg_of_le_pi positive.le
      (by linarith only [small_tilt, pi_pos])
    have curvature : 0 ≤ shallowDevelopmentCurvature φ := by
      unfold shallowDevelopmentCurvature
      exact mul_nonneg (by positivity) (sub_nonneg.mpr (cos_le_one φ))
    have nonneg : 0 ≤ shallowDevelopmentHeading φ := by
      unfold shallowDevelopmentHeading
      exact add_nonneg (add_nonneg (add_nonneg
        (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (arcsin_nonneg.mpr (sq_nonneg _))))
        (mul_nonneg (by positivity) sec))
        (mul_nonneg (by positivity) sin_nonneg)) (mul_nonneg (by norm_num) curvature)
    simpa only [equal, sub_self, abs_zero] using nonneg
  have before : i.val < j.val := (lt_of_le_of_ne ordered equal : i < j)
  let n := j.val - i.val - 1
  have fits : i.val + (n + 1) ≤ m := by
    have bound := j.isLt
    dsimp only [n]
    omega
  have j_eq : (⟨i.val + n + 1, by omega⟩ : Fin (m + 1)) = j := by
    apply Fin.ext
    change i.val + n + 1 = j.val
    dsimp only [n]
    omega
  have strictly := P.vertex_radius_strictMono_of_radial source radial
    (K.projectedBoundaryChain_edge_ne_zero full)
  have genuine (k : Fin (m + 2)) (past : 0 < k.val) : P.vertex k - source ≠ 0 := by
    intro zero
    have radius := strictly (show (0 : Fin (m + 2)) < k from past)
    change dist source (P.vertex 0) < dist source (P.vertex k) at radius
    rw [sub_eq_zero.mp zero, dist_self] at radius
    exact dist_nonneg.not_gt radius
  let sub := full.interval i.val (n + 1) fits
  let A := K.folding.projectedBoundaryChain sub
  have geometry : A = P.interval i.val (n + 2) (by omega) :=
    K.folding.projectedBoundaryChain_interval full i.val (n + 1) fits
  have actual_short : (∑ k : Fin n, angle (A.internalSourceRay source k.castSucc)
      (A.internalSourceRay source k.succ)) < π := by
    rw [geometry, P.interval_internal_angle_sum_in_frame_of_noninitial L source genuine, j_eq]
    exact short
  have actual_radial : A.RadialFrom source 0 := by
    rw [geometry]
    intro k _
    exact radial ⟨i.val + k.val, by omega⟩ (Nat.zero_le _)
  have actual_margin (k : Fin (n + 2)) :
      γ * (‖A.vertex k.castSucc - source‖ * ‖A.edge k‖) ≤
        inner ℝ (A.vertex k.castSucc - source) (A.edge k) := by
    rw [geometry]
    exact margin ⟨i.val + k.val, by omega⟩
  have estimate := K.abs_projectedMetricHeadingError_le_sharp_of_halfturn positive small_tilt
    height_bound tilt sub (fun k => cut (full.intervalIndex i.val (n + 1) fits k))
    source actual_radial margin_pos actual_margin actual_short
  have phase := K.projectedMetricHeadingError_interval full i.val (n + 1) fits (Fin.last (n + 1))
  have last_eq : (⟨i.val + (Fin.last (n + 1)).val, by omega⟩ : Fin (m + 1)) = j :=
    Fin.ext (by simpa only [Fin.val_last, Nat.add_assoc] using congrArg Fin.val j_eq)
  rw [last_eq] at phase
  exact (abs_sub_comm _ _).trans_le ((congrArg abs phase).symm.le.trans estimate)

end Unfoldings.ConvexRoof
