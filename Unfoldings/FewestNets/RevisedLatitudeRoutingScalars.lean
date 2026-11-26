module

public import Unfoldings.FewestNets.RevisedLatitudeVertexBounds
public import Unfoldings.Geometry.ArctanScalars
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.Jensen

/-! Coupled angle and area estimates at the actual band height. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real

/-- The normalized lower height times the denominator cutoff. -/
def heightDenominator (polar : Bool) (x : ℝ) : ℝ :=
  0.9612 * (x * (1 - 0.522 ^ 2 / 24) - ordinateErrorFactor polar * 0.268 ^ 2)

/-- Projection angle distortion divided by the input margin. -/
def distortionFactor (polar : Bool) (x : ℝ) : ℝ :=
  0.512 * 0.72 ^ 2 * ((0.268 / (2 * 0.9612)) ^ 2 +
    (x / (2 * 0.9612) + ordinateErrorFactor polar * 0.268 ^ 2) ^ 2)

/-- Upper coefficient of the apex angle. -/
def apexFactor (polar : Bool) (x : ℝ) : ℝ := 0.51 / heightDenominator polar x

/-- Upper coefficient of the sum of the cell area and the pole triangle area. -/
def areaFactor (polar : Bool) (x : ℝ) : ℝ :=
  (0.51 * 0.72 ^ 2 / (2 * 0.9612)) * (3 * x / (2 * 0.9612) +
    2 * ordinateErrorFactor polar * 0.268 ^ 2)

/-- The long-side ratio coefficient accounts for a refined polar row. -/
def sideFactor (polar : Bool) (x : ℝ) : ℝ :=
  (if polar then 0.8 else 1) * apexFactor polar x

private def band : Set ℝ := Set.Icc 0.852 1

private theorem heightDenominator_pos (polar : Bool) {x : ℝ} (hx : x ∈ band) :
    0 < heightDenominator polar x := by
  have low : 0.852 ≤ x := hx.1
  cases polar <;> norm_num [heightDenominator, ordinateErrorFactor] <;> linarith only [low]

private theorem sideFactor_bounds (polar : Bool) {x : ℝ} (hx : x ∈ band) :
    0 < sideFactor polar x ∧ sideFactor polar x ≤ 0.66 := by
  have low : 0.852 ≤ x := hx.1
  have h := heightDenominator_pos polar hx
  have normalize : sideFactor polar x =
      ((if polar then 0.8 else 1) * 0.51) / heightDenominator polar x := by
    unfold sideFactor apexFactor
    rw [mul_div_assoc]
  rw [normalize]
  refine ⟨div_pos (by cases polar <;> norm_num) h, (div_le_iff₀ h).mpr ?_⟩
  cases polar <;> norm_num [heightDenominator, ordinateErrorFactor] <;> linarith only [low]

private theorem areaFactor_lb (polar : Bool) {x : ℝ} (hx : x ∈ band) :
    0.185 ≤ areaFactor polar x := by
  have low : 0.852 ≤ x := hx.1
  cases polar <;> norm_num [areaFactor, ordinateErrorFactor] <;> linarith only [low]

private def affine (s t : ℝ) : ℝ →ᵃ[ℝ] ℝ := AffineMap.lineMap t (s + t)

private theorem affine_apply (s t x : ℝ) : affine s t x = s * x + t := by
  rw [affine, AffineMap.lineMap_apply_ring]
  ring

private def denominatorAffine (polar : Bool) : ℝ →ᵃ[ℝ] ℝ :=
  affine (0.9612 * (1 - 0.522 ^ 2 / 24)) (-0.9612 * ordinateErrorFactor polar * 0.268 ^ 2)

private theorem denominatorAffine_apply (polar : Bool) (x : ℝ) :
    denominatorAffine polar x = heightDenominator polar x := by
  rw [denominatorAffine, affine_apply, heightDenominator]
  ring

private theorem distortion_convex (polar : Bool) : ConvexOn ℝ band (distortionFactor polar) := by
  let A := affine (1 / (2 * 0.9612)) (ordinateErrorFactor polar * 0.268 ^ 2)
  have square : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
    Even.convexOn_pow (by decide : Even 2)
  have shifted := (square.comp_affineMap A).subset (Set.subset_univ band) (convex_Icc _ _)
  have expression : distortionFactor polar =
      fun x => (0.512 * 0.72 ^ 2 : ℝ) • ((A x) ^ 2 + (0.268 / (2 * 0.9612)) ^ 2) := by
    funext x
    rw [distortionFactor, smul_eq_mul, show A x = _ from affine_apply _ _ _]
    ring
  rw [expression]
  exact ConvexOn.smul (by norm_num) (shifted.add_const _)

private theorem area_convex (polar : Bool) : ConvexOn ℝ band (areaFactor polar) := by
  let A := affine ((0.51 * 0.72 ^ 2 / (2 * 0.9612)) * 3 / (2 * 0.9612))
    ((0.51 * 0.72 ^ 2 / (2 * 0.9612)) * (2 * ordinateErrorFactor polar * 0.268 ^ 2))
  have expression : areaFactor polar = A := by
    funext x
    rw [show A x = _ from affine_apply _ _ _, areaFactor]
    ring
  rw [expression]
  have h := (convexOn_id (𝕜 := ℝ) (convex_univ : Convex ℝ (Set.univ : Set ℝ))).comp_affineMap A
  exact h.subset (Set.subset_univ band) (convex_Icc _ _)

private theorem apex_convex (polar : Bool) : ConvexOn ℝ band (apexFactor polar) := by
  have pulled := convexOn_inv_pos.comp_affineMap (denominatorAffine polar)
  have bounded := pulled.subset (fun x hx => by
    change 0 < denominatorAffine polar x
    rw [denominatorAffine_apply]
    exact heightDenominator_pos polar hx) (convex_Icc _ _)
  have scaled := ConvexOn.smul (show 0 ≤ (0.51 : ℝ) by norm_num) bounded
  have ident : apexFactor polar = fun x => (0.51 : ℝ) • (denominatorAffine polar x)⁻¹ := by
    funext x
    rw [denominatorAffine_apply, smul_eq_mul, apexFactor, div_eq_mul_inv]
  rw [ident]
  exact scaled

private theorem side_convex (polar : Bool) {A : ℝ} (ap : 0 < A) :
    ConvexOn ℝ band (fun x => arctan (A * sideFactor polar x) / A) := by
  let c : ℝ := A * (if polar then 0.8 else 1) * 0.51
  have cp : 0 < c := by cases polar <;> dsimp [c] <;> positivity
  have pulled := (convexOn_arctan_div cp).comp_affineMap (denominatorAffine polar)
  have bounded := pulled.subset (fun x hx => by
    change 0 < denominatorAffine polar x
    rw [denominatorAffine_apply]
    exact heightDenominator_pos polar hx) (convex_Icc _ _)
  have scaled := ConvexOn.smul (show (0 : ℝ) ≤ A⁻¹ by positivity) bounded
  have equal : (fun x => arctan (A * sideFactor polar x) / A) =
      fun x => A⁻¹ • arctan (c / denominatorAffine polar x) := by
    funext x
    rw [smul_eq_mul, denominatorAffine_apply, div_eq_mul_inv, mul_comm A⁻¹]
    congr 2
    unfold sideFactor apexFactor c
    ring
  rw [equal]
  exact scaled

private theorem first_endpoint (polar : Bool) (x : ℝ) (hx : x = 0.852 ∨ x = 1) :
    3 * distortionFactor polar x + 2 * (11 / 21 : ℝ) * areaFactor polar x +
      arctan ((11 / 21 : ℝ) * sideFactor polar x) / (11 / 21 : ℝ) < 1 := by
  have in_band : x ∈ band := by rcases hx with rfl | rfl <;> norm_num [band]
  have sine := arctan_le_fifth
    (show 0 ≤ (11 / 21 : ℝ) * sideFactor polar x from
      mul_nonneg (by norm_num) (sideFactor_bounds polar in_band).1.le)
  have scaled := div_le_div_of_nonneg_right sine (show 0 ≤ (11 / 21 : ℝ) by norm_num)
  rcases hx with rfl | rfl <;> cases polar <;>
    norm_num [distortionFactor, areaFactor, sideFactor, apexFactor, heightDenominator,
      ordinateErrorFactor] at scaled ⊢ <;> linarith only [scaled]

private theorem second_endpoint (polar : Bool) (x : ℝ) (hx : x = 0.852 ∨ x = 1) :
    2 * distortionFactor polar x + (11 / 21 : ℝ) * areaFactor polar x + apexFactor polar x < 1 := by
  rcases hx with rfl | rfl <;> cases polar <;>
    norm_num [distortionFactor, areaFactor, apexFactor, heightDenominator, ordinateErrorFactor]

/-- Both clearance inequalities hold simultaneously over every admissible
band height and margin, using the exact polar-row refinement on the sides. -/
theorem revised_routing_margins (polar : Bool) {a x : ℝ} (ap : 0 < a) (amax : a ≤ 11 / 21)
    (xmin : 0.852 ≤ x) (xmax : x ≤ 1) :
    let d := distortionFactor polar x
    let u := apexFactor polar x
    let V := areaFactor polar x
    3 * d + 2 * a * V + arctan (a * sideFactor polar x) / a < 1 ∧
      2 * d + a * V + u < 1 := by
  let A : ℝ := 11 / 21
  let d := distortionFactor polar x
  let u := apexFactor polar x
  let V := areaFactor polar x
  let y := sideFactor polar x
  have hx : x ∈ band := ⟨xmin, xmax⟩
  have h0 : (0.852 : ℝ) ∈ band := by norm_num [band]
  have h1 : (1 : ℝ) ∈ band := by norm_num [band]
  have aprop : 0 < A := by norm_num [A]
  have a_le : a ≤ A := amax
  have cy := side_convex polar aprop
  have cd := distortion_convex polar
  have cV := area_convex polar
  have cu := apex_convex polar
  have vf : 0.185 ≤ V := areaFactor_lb polar hx
  have yp : 0 < y := (sideFactor_bounds polar hx).1
  have ycap : y ≤ 0.66 := (sideFactor_bounds polar hx).2
  have comp : (A + a) * y ^ 3 / 3 ≤ 2 * V := by
    have cubed := pow_le_pow_left₀ yp.le ycap 3
    have sum : A + a ≤ 2 * A := by linarith only [a_le]
    have h := mul_le_mul sum cubed (pow_nonneg yp.le _) (show 0 ≤ 2 * A by positivity)
    dsimp [A] at h
    linarith only [h, vf]
  have cost := mul_le_mul_of_nonneg_right comp (sub_nonneg.mpr a_le)
  have change_scale := scaled_arctan_difference_le ap a_le yp.le
  have eq : (A ^ 2 - a ^ 2) * y ^ 3 / 3 = ((A + a) * y ^ 3 / 3) * (A - a) := by ring
  rw [eq] at change_scale
  have inc : 2 * a * V + arctan (a * y) / a ≤ 2 * A * V + arctan (A * y) / A := by
    linarith only [change_scale, show ((A + a) * y ^ 3 / 3) * (A - a) ≤
      2 * A * V - 2 * a * V by linarith only [cost]]
  have add_convex {f g : ℝ → ℝ} (cf : ConvexOn ℝ band f) (cg : ConvexOn ℝ band g) :
      ConvexOn ℝ band (fun x => f x + g x) := by
    have eq : f + g = fun t => f t + g t := funext (fun t => Pi.add_apply f g t)
    exact eq ▸ cf.add cg
  have f1 : ConvexOn ℝ band (fun z => 3 * distortionFactor polar z +
      2 * A * areaFactor polar z + arctan (A * sideFactor polar z) / A) := by
    simpa only [smul_eq_mul] using add_convex
      (add_convex (ConvexOn.smul (show 0 ≤ (3 : ℝ) by norm_num) cd)
        (ConvexOn.smul (show 0 ≤ 2 * A by positivity) cV)) cy
  have f2 : ConvexOn ℝ band (fun z => 2 * distortionFactor polar z +
      A * areaFactor polar z + apexFactor polar z) := by
    simpa only [smul_eq_mul] using add_convex
      (add_convex (ConvexOn.smul (show 0 ≤ (2 : ℝ) by norm_num) cd)
        (ConvexOn.smul aprop.le cV)) cu
  have bound₁ := (f1.le_max_of_mem_Icc h0 h1 hx).trans_lt
    (max_lt (first_endpoint polar _ (Or.inl rfl)) (first_endpoint polar _ (Or.inr rfl)))
  have bound₂ := (f2.le_max_of_mem_Icc h0 h1 hx).trans_lt
    (max_lt (second_endpoint polar _ (Or.inl rfl)) (second_endpoint polar _ (Or.inr rfl)))
  change 3 * d + 2 * a * V + arctan (a * y) / a < 1 ∧ 2 * d + a * V + u < 1
  refine ⟨?_, ?_⟩
  · change 3 * d + 2 * A * V + arctan (A * y) / A < 1 at bound₁
    linarith only [inc, bound₁]
  · have smaller := mul_le_mul_of_nonneg_right a_le (show 0 ≤ V by linarith only [vf])
    change 2 * d + A * V + u < 1 at bound₂
    linarith only [smaller, bound₂]

end Unfoldings.FewestNets.RevisedLatitudeGrid
