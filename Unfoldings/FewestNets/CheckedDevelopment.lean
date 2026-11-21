module

public import Unfoldings.FewestNets.CheckedInverseTrig
public import Unfoldings.Geometry.SharpDevelopmentThreshold

/-! Evaluate the three numerical conditions of the sharp development bound. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real CheckedReal

/-- The signed gaps in the three sufficient conditions of the paper. -/
def developmentGaps (phi gamma length : ℝ) : Fin 3 → ℝ :=
  let omega := shallowDevelopmentCurvature phi
  let B := shallowDevelopmentHeading phi
  let E := radialBlockError (cos phi)⁻¹ B length (Real.sqrt (1 - gamma ^ 2)) π
  let d := (gamma - E) / (1 + E)
  let D := length * (cos phi)⁻¹ / (1 - E)
  ![gamma - E, (d - 3 * omega * D) / (1 + 3 * omega * D) - 2 * omega / π,
    2 * arcsin gamma - (B + 3 * omega)]

/-- Check the gaps from just the tilt, radial margin, and length constant. -/
def checkDevelopmentGaps {D : ℕ} (hD : 0 < D) {phi gamma length : ℝ}
    (cp : CheckedReal D phi) (cg : CheckedReal D gamma) (cl : CheckedReal D length)
    (argument_small : tan (phi / 2) ^ 2 < 1) (gamma_nonneg : 0 ≤ gamma)
    (gamma_small : gamma < 1) (order : ℕ) :
    (i : Fin 3) → CheckedReal D (developmentGaps phi gamma length i) :=
  let one : CheckedReal D (1 : ℝ) := (rat D 1).convert (by simp)
  let two : CheckedReal D (2 : ℝ) := (rat D 2).convert (by simp)
  let three : CheckedReal D (3 : ℝ) := (rat D 3).convert (by simp)
  let six : CheckedReal D (6 : ℝ) := (rat D 6).convert (by simp)
  let p := checkPi D
  let c := cp.checkCos hD order
  let sec := (one.div hD c).convert (one_div _)
  let omega := (two.mul hD p).mul hD (one.sub c)
  let tan := (cp.div hD two).checkTan hD order
  let delta := two.mul hD ((tan.square hD).checkArcsin hD (sq_nonneg _) argument_small)
  let B := ((three.mul hD delta).add ((two.mul hD p).mul hD (sec.sub one))).add
    ((six.mul hD cp).mul hD (cp.checkSin hD order)) |>.add (two.mul hD omega)
  let root := (one.sub (cg.square hD)).sqrt hD
  let E := (cl.mul hD (sec.sub one)).add
    (((sec.mul hD B).mul hD cl).mul hD (one.add ((cl.mul hD root).div hD p)))
  let gap := cg.sub E
  let d := gap.div hD (one.add E)
  let s := (cl.mul hD sec).div hD (one.sub E)
  let tail := (three.mul hD omega).mul hD s
  let m := (d.sub tail).div hD (one.add tail)
  let fresh := m.sub ((two.mul hD omega).div hD p)
  let wedge := (two.mul hD (cg.checkArcsin hD gamma_nonneg gamma_small)).sub
    (B.add (three.mul hD omega))
  Fin.cases gap (Fin.cases fresh (Fin.cases wedge (fun i => Fin.elim0 i)))

/-- A successful check proves all three real inequalities. -/
theorem developmentGaps_pos_of_check {D : ℕ} (hD : 0 < D) {phi gamma length : ℝ}
    (cp : CheckedReal D phi) (cg : CheckedReal D gamma) (cl : CheckedReal D length)
    (argument_small : tan (phi / 2) ^ 2 < 1) (gamma_nonneg : 0 ≤ gamma)
    (gamma_small : gamma < 1) (order : ℕ)
    (check : (List.finRange 3).all (fun i =>
      (checkDevelopmentGaps hD cp cg cl argument_small gamma_nonneg gamma_small order i).isPositive)
        = true) :
    let omega := shallowDevelopmentCurvature phi
    let B := shallowDevelopmentHeading phi
    let E := radialBlockError (cos phi)⁻¹ B length (Real.sqrt (1 - gamma ^ 2)) π
    let d := (gamma - E) / (1 + E)
    let D := length * (cos phi)⁻¹ / (1 - E)
    E < gamma ∧ 2 * omega / π < (d - 3 * omega * D) / (1 + 3 * omega * D) ∧
      B + 3 * omega < 2 * arcsin gamma := by
  have h (i : Fin 3) : 0 < developmentGaps phi gamma length i :=
    positive_of_isPositive hD _ (List.all_eq_true.mp check i (List.mem_finRange i))
  exact ⟨sub_pos.mp (h 0), sub_pos.mp (h 1), sub_pos.mp (h 2)⟩

end Unfoldings.FewestNets
