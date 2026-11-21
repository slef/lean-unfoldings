module

public import Unfoldings.FewestNets.FiniteDevelopmentScalarBlocks
public import Unfoldings.FewestNets.CheckedMeshStar
public import Unfoldings.FewestNets.IcosahedronMeshTilt

/-! Validate the record tilt by the uniform cover or the physical gnomonic radius. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeshStar Real

/-- Rational test for the uniform angle bound, using the exact square of √5. -/
def checkUniformRecordTilt (q : ℕ) (tilt : ℚ) : Bool :=
  let s := 3 - (q : ℚ) * tilt
  decide (s ≤ 0) || decide (s ^ 2 ≤ 5)

theorem meshTilt_le_of_checkUniformRecordTilt {q : ℕ} (positive : 0 < q) {φ : ℚ}
    (pass : checkUniformRecordTilt q φ = true) : Icosahedron.meshTilt q ≤ φ := by
  have qr : (0 : ℝ) < q := by exact_mod_cast positive
  unfold Icosahedron.meshTilt
  apply (div_le_iff₀ qr).mpr
  have bound : (3 : ℝ) - (q : ℝ) * φ ≤ sqrt 5 := by
    simp only [checkUniformRecordTilt, Bool.or_eq_true, decide_eq_true_eq] at pass
    rcases pass with below | square
    · have below' : (3 : ℝ) - (q : ℝ) * φ ≤ 0 := by exact_mod_cast below
      exact below'.trans (sqrt_nonneg _)
    · have square' : ((3 : ℝ) - (q : ℝ) * φ) ^ 2 ≤ 5 := by exact_mod_cast square
      by_cases positive : 0 ≤ (3 : ℝ) - (q : ℝ) * φ
      · exact (le_sqrt positive (by norm_num)).mpr square'
      · exact (le_of_lt (lt_of_not_ge positive)).trans (sqrt_nonneg _)
  linarith only [bound]

namespace MeshStar.Checked

variable {n D : ℕ} {M : MeshStar (n + 1)} (hD : 0 < D) (Mchecked : MeshStar.Checked D M)

/-- The radius test works in spatial tangent coordinates, so it is invariant
under the frame realizing the model at an actual site. -/
def checkGnomonicRadius (tilt : ℚ) : Bool :=
  let limit := (CheckedReal.rat D tilt).checkTan hD 12
  (List.finRange (n + 1)).all fun k =>
    (CheckedSpace.norm hD (Mchecked.gnomonicVertex hD k)).isLT limit

theorem gnomonicVertex_norm_le_tan_of_check {tilt : ℚ}
    (pass : checkGnomonicRadius hD Mchecked tilt = true) (i : Fin (n + 1)) :
    ‖M.gnomonicVertex i‖ ≤ Real.tan tilt :=
  (CheckedReal.lt_of_isLT hD _ _ (List.all_eq_true.mp pass i (List.mem_finRange i))).le

end MeshStar.Checked

/-- Check the tilt of a record using the model named by its key. -/
def checkDevelopmentCellTilt (q : ℕ) (key : MeshRecordKey) (φ : ℚ) : Bool :=
  let h := certificateDenominator_pos
  checkUniformRecordTilt q φ ||
    match key with
    | .face i j => MeshStar.Checked.checkGnomonicRadius h (checkFace h q i j) φ
    | .seam i => MeshStar.Checked.checkGnomonicRadius h (checkSeam h q i) φ
    | .vertex => MeshStar.Checked.checkGnomonicRadius h (checkPentagon h q) φ

end Unfoldings.FewestNets
