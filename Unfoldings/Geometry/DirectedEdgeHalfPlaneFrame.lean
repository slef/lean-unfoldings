module

public import Unfoldings.Geometry.EdgeHalfPlaneMetric
public import Unfoldings.Geometry.EdgeSides
public import Unfoldings.Geometry.Endpoints
public import Mathlib.Analysis.Complex.Isometry
public import Unfoldings.Metric.BankHalfPlaneFrames

/-! Rigid coordinates for a triangle bank preserve its directed arclength. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

open MetricGluing

/-- A half-plane frame can put the occupied side above or below the real axis
while retaining the original directed bank arclength. -/
theorem exists_directedEdgeHalfPlaneFrame (T : Triangle) (edge : Fin 3)
    (start occupied : Bool) (t : unitInterval) :
    let p := (T.endpoint edge start).val
    let q := (T.endpoint edge (!start)).val
    ∃ F : Plane ≃ᵃⁱ[ℝ] ℂ,
      (∀ s : ℝ, F (AffineMap.lineMap p q s) = (((s - t.val) * ‖q - p‖ : ℝ) : ℂ)) ∧
      ∀ x, F x ∈ bankHalfPlane occupied ↔ x ∈ T.edgeHalfPlane edge := by
  dsimp only
  let p := (T.endpoint edge start).val
  let q := (T.endpoint edge (!start)).val
  let P := Complex.orthonormalBasisOneI.repr.symm
  let d := P (q - p)
  let U := P.trans (rotation (Circle.exp d.arg)).symm
  have direction : U (q - p) = (‖q - p‖ : ℂ) := by
    change (rotation (Circle.exp d.arg)).symm d = _
    apply (rotation (Circle.exp d.arg)).injective
    rw [LinearIsometryEquiv.apply_symm_apply, rotation_apply]
    have norm := P.norm_map (q - p)
    change ‖d‖ = ‖q - p‖ at norm
    rw [← norm, mul_comm]
    exact (Complex.norm_mul_exp_arg_mul_I d).symm
  let F := (AffineIsometryEquiv.vaddConst ℝ (AffineMap.lineMap p q t.val)).symm.trans
    U.toAffineIsometryEquiv
  have param (s : ℝ) : F (AffineMap.lineMap p q s) =
      (((s - t.val) * ‖q - p‖ : ℝ) : ℂ) := by
    change U (AffineMap.lineMap p q s - AffineMap.lineMap p q t.val) = _
    have delta : AffineMap.lineMap p q s - AffineMap.lineMap p q t.val =
        (s - t.val) • (q - p) := by
      rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module',
        add_sub_add_right_eq_sub, sub_smul]
    rw [delta, map_smul, direction, Complex.real_smul, Complex.ofReal_mul]
  let height := Complex.imCLM.toLinearMap.toAffineMap.comp F.toAffineEquiv.toAffineMap
  have pzero : height p = 0 := by
    change (F p).im = 0
    simpa only [AffineMap.lineMap_apply_zero, Complex.ofReal_im] using
      congrArg Complex.im (param 0)
  have qzero : height q = 0 := by
    change (F q).im = 0
    simpa only [AffineMap.lineMap_apply_one, Complex.ofReal_im] using
      congrArg Complex.im (param 1)
  have altitude (x : Plane) : height x =
      height (T.opposite edge) * T.coord (next (next edge)) x := by
    apply T.affine_height_eq_coord edge height
    · cases start
      · exact pzero
      · exact qzero
    · cases start
      · exact qzero
      · exact pzero
  have nonzero : height (T.opposite edge) ≠ 0 := by
    intro hz
    have impossible := altitude (F.symm Complex.I)
    rw [hz, zero_mul] at impossible
    change (F (F.symm Complex.I)).im = 0 at impossible
    rw [F.apply_symm_apply, Complex.I_im] at impossible
    exact one_ne_zero impossible
  let flip := decide ((0 < height (T.opposite edge)) ↔ occupied = true)
  let N := bankAxisFrame false flip
  refine ⟨F.trans N.toAffineIsometryEquiv, ?_, ?_⟩
  · intro s
    change N (F (AffineMap.lineMap p q s)) = _
    rw [param]
    exact bankAxisFrame_ofReal false flip _
  · intro x
    change N (F x) ∈ bankHalfPlane occupied ↔ 0 ≤ T.coord (next (next edge)) x
    have physical : (F x).im = height (T.opposite edge) * T.coord (next (next edge)) x :=
      altitude x
    rcases lt_or_gt_of_ne nonzero with neg | pos
    · have sign : ¬ 0 < height (T.opposite edge) := not_lt_of_gt neg
      have criterion : height (T.opposite edge) * T.coord (next (next edge)) x ≤ 0 ↔
          0 ≤ T.coord (next (next edge)) x := by
        constructor
        · intro h
          by_contra hn
          exact (not_lt_of_ge h) (mul_pos_of_neg_of_neg neg (lt_of_not_ge hn))
        · exact mul_nonpos_of_nonpos_of_nonneg neg.le
      cases occupied <;> simp [N, bankHalfPlane, bankAxisFrame_im, flip, physical, sign, criterion]
    · cases occupied <;> simp [N, bankHalfPlane, bankAxisFrame_im, flip, physical, pos]

end Unfoldings.Triangle
