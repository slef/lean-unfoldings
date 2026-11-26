module

public import Unfoldings.FewestNets.RevisedLatitudeRoutingScalars
public import Unfoldings.FewestNets.RevisedLatitudeTilt
public import Unfoldings.FewestNets.AcuteLatitudeRouting

/-! The new geometric budgets instantiate the actual three-exit routing. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open FewestNets FewestNets.RevisedLatitudeGrid Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C)

private theorem arctan_sub_le {u v : ℝ} (order : u < v) :
    arctan v - arctan u ≤ v - u := by
  obtain ⟨c, _, slope⟩ := exists_deriv_eq_slope arctan order
    continuous_arctan.continuousOn differentiable_arctan.differentiableOn
  rw [Real.deriv_arctan] at slope
  change 1 / (1 + c ^ 2) = (arctan v - arctan u) / (v - u) at slope
  have bound : 1 / (1 + c ^ 2) ≤ 1 :=
    (div_le_one₀ (by positivity)).mpr (by linarith only [sq_nonneg c])
  rw [slope] at bound
  simpa only [one_mul] using (div_le_iff₀ (sub_pos.mpr order)).mp bound

private theorem abs_arctan_eq (x : ℝ) : |arctan x| = arctan |x| := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (arctan_nonneg.mpr h)]
  · have nn : arctan x ≤ 0 := by simpa only [arctan_zero] using arctan_mono h
    rw [abs_of_nonpos h, arctan_neg, abs_of_nonpos nn]

set_option maxHeartbeats 1800000 in
/-- The revised normalized geometric bounds leave a strict reserve in every
actual history window for the signed normal-area turn bound. -/
theorem exists_revisedLatitudeTriangleRouting (seed : Face) (polar : Bool)
    {a x φ left right base apex height : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6) (xlo : 0.852 ≤ x) (xhi : x ≤ 1)
    (tilt_pos : 0 < φ) (tilt_small : φ ≤ 0.297)
    (tilt : 0.512 * φ ^ 2 ≤ a * distortionFactor polar x)
    (base_pos : left < right) (height_pos : 0 < height)
    (apex_bound : (right - left) / height ≤ a * apexFactor polar x)
    (east_ratio : |latitudeEastRatio right apex height| ≤ a * sideFactor polar x)
    (west_ratio : |latitudeWestRatio left apex height| ≤ a * sideFactor polar x)
    (radius : ∀ p ∈ latitudeSlopeTriangle left right base apex height, ‖p‖ ≤ tan φ)
    (generic : ∀ f, K.normalSlope f ∉ frontier (latitudeSlopeTriangle left right base apex height))
    (selected : K.normalSlope seed ∈ latitudeSlopeTriangle left right base apex height)
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ π / 2 - a) :
    let B := latitudeTriangleSideDirections left right base apex height base_pos height_pos
    let compact := isCompact_latitudeSlopeTriangle left right base apex height
    let present := Set.nonempty_of_mem selected
    let budget := a * (distortionFactor polar x + a * areaFactor polar x)
    ∃ σ > budget, ∃ (H : ThreeExitStemWindows)
      (R : K.ThreeExitComponentRouting seed B compact present H),
      0 ≤ π / 2 - σ ∧
      ∀ r : {r // r ∈ R.stems.choice.parents.roots},
        let exit := (R.rootHeadingChart r (R.rootExitDirection r)).arg
        let lo := R.rootWindowStart r
        max (lo + H.width) exit - min lo exit ≤ π / 2 - σ := by
  dsimp only
  let S := latitudeSlopeTriangle left right base apex height
  let B := latitudeTriangleSideDirections left right base apex height base_pos height_pos
  let compact := isCompact_latitudeSlopeTriangle left right base apex height
  let present := Set.nonempty_of_mem selected
  let D := distortionFactor polar x
  let V := areaFactor polar x
  let U := apexFactor polar x
  let y := sideFactor polar x
  let b := a * (D + a * V)
  let δ := (a - a * D) / 2
  let e := arctan (latitudeEastRatio right apex height)
  let w := arctan (latitudeWestRatio left apex height)
  have amax : a ≤ 11 / 21 := by linarith only [small, pi_lt_d6]
  obtain ⟨one, two⟩ := revised_routing_margins polar positive amax xlo xhi
  change 3 * D + 2 * a * V + arctan (a * y) / a < 1 at one
  change 2 * D + a * V + U < 1 at two
  have Dn : 0 ≤ D := by dsimp [D, distortionFactor]; positivity
  have Vn : 0 ≤ V := by
    have e_nonneg : 0 ≤ ordinateErrorFactor polar := by cases polar <;> norm_num [ordinateErrorFactor]
    have x_nonneg : 0 ≤ x := by linarith only [xlo]
    dsimp only [V, areaFactor]
    positivity
  have bn : 0 ≤ b := by dsimp only [b]; positivity
  have yn : 0 ≤ a * y := (abs_nonneg _).trans east_ratio
  have en : |e| ≤ arctan (a * y) := by rw [show |e| = _ from abs_arctan_eq _]; exact arctan_mono east_ratio
  have wn : |w| ≤ arctan (a * y) := by rw [show |w| = _ from abs_arctan_eq _]; exact arctan_mono west_ratio
  have spread : w - e ≤ a * U := by
    let u := latitudeEastRatio right apex height
    let v := latitudeWestRatio left apex height
    have eq : v - u = (right - left) / height := by
      dsimp only [u, v, latitudeEastRatio, latitudeWestRatio]
      rw [← sub_div]
      congr 1
      ring
    have order : u < v := sub_pos.mp (eq.symm ▸ div_pos (sub_pos.mpr base_pos) height_pos)
    exact (arctan_sub_le order).trans (eq.symm ▸ apex_bound)
  have first : 2 * b + a * D + arctan (a * y) < a := by
    have scaled := mul_lt_mul_of_pos_right one positive
    have identity : (3 * D + 2 * a * V + arctan (a * y) / a) * a =
        2 * b + a * D + arctan (a * y) := by
      dsimp only [b]
      field_simp [positive.ne']
      ring
    rwa [identity, one_mul] at scaled
  have second : b + a * D + a * U < a := by
    have h := mul_lt_mul_of_pos_left two positive
    dsimp only [b]
    nlinarith only [h]
  have ae : 0 ≤ arctan (a * y) := arctan_nonneg.mpr yn
  have de : |e| < 2 * δ := by dsimp only [δ]; linarith only [en, first, bn, Dn]
  have dw : |w| < 2 * δ := by dsimp only [δ]; linarith only [wn, first, bn, Dn]
  let ceiling := min δ (min (δ + e / 2) (min (δ - w / 2) (2 * δ + e - w)))
  have room : b < ceiling := by
    unfold ceiling
    rw [lt_min_iff, lt_min_iff, lt_min_iff]
    dsimp only [δ]
    exact ⟨by linarith only [first, ae], by linarith only [first, (abs_le.mp en).1],
      by linarith only [first, (abs_le.mp wn).2], by linarith only [second, spread]⟩
  let σ := (b + ceiling) / 2
  have above : b < σ := by dsimp only [σ]; linarith only [room]
  have below : σ < ceiling := by dsimp only [σ]; linarith only [room]
  have σ_pos : 0 < σ := bn.trans_lt above
  have σ_le : σ ≤ δ := below.le.trans (min_le_left _ _)
  have δ_cap : δ ≤ π / 8 := by
    dsimp only [δ]
    linarith only [small, mul_nonneg positive.le Dn, pi_pos]
  have σ_e : σ < δ + e / 2 := below.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have σ_w : σ < δ - w / 2 :=
    below.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have σ_cross : σ < 2 * δ + e - w :=
    below.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have span_nonneg : 0 ≤ π / 2 - σ := by linarith only [σ_le, δ_cap, pi_pos]
  have tilt_lt : φ < π / 2 := by linarith only [tilt_small, pi_gt_d2]
  have cos_pos : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith only [tilt_pos, pi_pos], tilt_lt⟩
  have correction := (revised_projection_allowance_le_sq tilt_pos.le tilt_small).trans tilt
  have projected (f : Face) (hf : f ∈ K.selectionComponent S seed) (i : Fin 3) :
      (K.projectedTriangle f).cornerAngle i ≤ π / 2 - 2 * δ := by
    have belongs := K.selectionComponent_selected selected hf
    have lower : cos φ ≤ K.normal f 2 := by
      let plane := SpatialPlane.ofGraph 0 (K.normalSlope f)
      have equiv : Cap.gnomonicNormal (K.normalSlope f) = plane.normal := by
        have same : plane.normalSlope = K.normalSlope f := SpatialPlane.ofGraph_normalSlope _ _
        rw [← same]
        exact Cap.gnomonicNormal_slope _ plane.normal_unit plane.normal_upward
      rw [← K.gnomonicNormal_normalSlope f, equiv]
      exact SpatialPlane.ofGraph_normal_height_of_slope_radius tilt_pos tilt_lt 0 _ (radius _ belongs)
    have allowance := K.projected_cornerAngle_le_of_normal_height cos_pos f lower i (angles f i)
    dsimp only [δ]
    linarith only [allowance, correction]
  have e_arg : (exitHeadingChart false (B.normal 0)).arg = e :=
    latitudeTriangle_east_arg left right base apex height base_pos height_pos
  have w_arg : (exitHeadingChart true (B.normal 1)).arg = -w :=
    latitudeTriangle_west_arg left right base apex height base_pos height_pos
  have n_arg : ∀ side, (exitHeadingChart side (B.normal 2)).arg = π / 2 :=
    latitudeTriangle_north_arg left right base apex height base_pos height_pos
  obtain ⟨H, ⟨R⟩, r_e, r_w, n_e, n_w⟩ := K.exists_threeExitComponentRouting_of_signed_headings
    seed B compact present σ_pos σ_le δ_cap de dw σ_e σ_w σ_cross projected e_arg w_arg generic selected
  exact ⟨σ, above, H, R, span_nonneg, R.root_span_of_signed_headings span_nonneg e_arg w_arg n_arg r_e r_w n_e n_w⟩

end Unfoldings.ConvexRoof
