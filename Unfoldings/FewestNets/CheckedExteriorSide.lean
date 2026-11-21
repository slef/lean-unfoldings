module

public import Unfoldings.FewestNets.CheckedVisualSide
public import Unfoldings.FewestNets.ExteriorCertificate

/-! Verify saved exterior progress witnesses along a complete polygon side. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

def exteriorNormalUpper (n p q w : Plane) : ℝ :=
  max (inner ℝ n (p - w)) (inner ℝ n (q - w))

def exteriorTangentLower (sign : Bool) (n p q w : Plane) : ℝ :=
  min (SideVisualWitness.signedCot sign (certificateOrientation.areaForm n (p - w)))
    (SideVisualWitness.signedCot sign (certificateOrientation.areaForm n (q - w)))

/-- Test one witness's endpoint normal distances, signed tangent displacement,
and squared polar-margin comparison. -/
def checkExteriorWitness {D : ℕ} (hD : 0 < D) (sign : Bool)
    {n p q w : Plane} {γ : ℝ} (cn : CheckedPlane D n) (cp : CheckedPlane D p)
    (cq : CheckedPlane D q) (cw : CheckedPlane D w) (cg : CheckedReal D γ) : Bool :=
  let r := CheckedPlane.sub cp cw
  let s := CheckedPlane.sub cq cw
  let a := CheckedPlane.dot hD cn r
  let b := CheckedPlane.dot hD cn s
  let A := a.maximum hD b
  let δp := SideVisualWitness.checkSignedCot (CheckedPlane.det hD cn r) sign
  let δq := SideVisualWitness.checkSignedCot (CheckedPlane.det hD cn s) sign
  let δ := δp.minimum hD δq
  let squared := δ.square hD
  (a.isPositive && b.isPositive) && (δ.isPositive &&
    ((cg.square hD).mul hD ((A.square hD).add squared)).isLT squared)

private theorem SideVisualWitness.signedCot_add_smul (sign : Bool) (p q t : ℝ) :
    SideVisualWitness.signedCot sign ((1 - t) * p + t * q) =
      (1 - t) * SideVisualWitness.signedCot sign p + t * SideVisualWitness.signedCot sign q := by
  cases sign
  · simp only [SideVisualWitness.signedCot, Bool.false_eq_true, ite_false]
    ring
  · simp [SideVisualWitness.signedCot]

/-- Successful endpoint tests hold with a uniform choice of normal and
tangential bounds on the full closed side. -/
theorem exteriorWitness_of_check {D : ℕ} (hD : 0 < D) (sign : Bool)
    {n p q w : Plane} {γ : ℝ} (cn : CheckedPlane D n) (cp : CheckedPlane D p)
    (cq : CheckedPlane D q) (cw : CheckedPlane D w) (cg : CheckedReal D γ)
    (pass : checkExteriorWitness hD sign cn cp cq cw cg = true)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    let x := AffineMap.lineMap p q t - w
    let A := exteriorNormalUpper n p q w
    let δ := exteriorTangentLower sign n p q w
    0 < δ ∧ 0 < inner ℝ n x ∧ inner ℝ n x ≤ A ∧
      δ ≤ SideVisualWitness.signedCot sign (certificateOrientation.areaForm n x) ∧
      γ ^ 2 * (A ^ 2 + δ ^ 2) ≤ δ ^ 2 := by
  let x := AffineMap.lineMap p q t - w
  let A := exteriorNormalUpper n p q w
  let δ := exteriorTangentLower sign n p q w
  unfold checkExteriorWitness at pass
  dsimp only at pass
  simp only [Bool.and_eq_true] at pass
  have p_pos := CheckedReal.positive_of_isPositive hD _ pass.1.1
  have q_pos := CheckedReal.positive_of_isPositive hD _ pass.1.2
  have δ_pos := CheckedReal.positive_of_isPositive hD _ pass.2.1
  have ratio := (CheckedReal.lt_of_isLT hD _ _ pass.2.2).le
  simp only [← areaForm_certificateOrientation] at δ_pos ratio
  change 0 < δ at δ_pos
  change γ ^ 2 * (A ^ 2 + δ ^ 2) ≤ δ ^ 2 at ratio
  have displacement : x = (1 - t) • (p - w) + t • (q - w) := by
    dsimp [x]
    rw [AffineMap.lineMap_apply_module]
    module
  have weights : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have normal : inner ℝ n x = (1 - t) * inner ℝ n (p - w) + t * inner ℝ n (q - w) := by
    rw [displacement, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have tangent : SideVisualWitness.signedCot sign (certificateOrientation.areaForm n x) =
      (1 - t) * SideVisualWitness.signedCot sign (certificateOrientation.areaForm n (p - w)) +
        t * SideVisualWitness.signedCot sign (certificateOrientation.areaForm n (q - w)) := by
    rw [displacement, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      SideVisualWitness.signedCot_add_smul]
  refine ⟨δ_pos, ?_, ?_, ?_, ratio⟩
  · rw [normal]
    rcases lt_or_eq_of_le ht.2 with left | last
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr left) p_pos)
        (mul_nonneg ht.1 q_pos.le)
    · simpa [last] using q_pos
  · rw [normal]
    have hp : inner ℝ n (p - w) ≤ A := le_max_left _ _
    have hq : inner ℝ n (q - w) ≤ A := le_max_right _ _
    have h := add_le_add (mul_le_mul_of_nonneg_left hp weights)
      (mul_le_mul_of_nonneg_left hq ht.1)
    rw [show (1 - t) * A + t * A = A by ring] at h
    exact h
  · rw [tangent]
    have hp : δ ≤ SideVisualWitness.signedCot sign
        (certificateOrientation.areaForm n (p - w)) := min_le_left _ _
    have hq : δ ≤ SideVisualWitness.signedCot sign
        (certificateOrientation.areaForm n (q - w)) := min_le_right _ _
    have h := add_le_add (mul_le_mul_of_nonneg_left hp weights)
      (mul_le_mul_of_nonneg_left hq ht.1)
    rw [show (1 - t) * δ + t * δ = δ by ring] at h
    exact h

end Unfoldings.FewestNets
