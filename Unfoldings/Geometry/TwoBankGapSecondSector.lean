module

public import Unfoldings.Geometry.TwoBankGapConeFrontier
public import Unfoldings.Geometry.TwoBankGapSecondWitness
public import Unfoldings.Cone.RotatedSectorRecognition
public import Unfoldings.Cone.ReentrantCornerChart

/-! Construct actual internal gap-bank sector charts from the original rays and radial side. -/

@[expose] public section

noncomputable section

open Filter Topology
open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ m)
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

/-- The first bank is absent near a nonsource point of the second actual bank. -/
theorem frontier_twoBankGap_cone_at_second_bank (common : Q.start = R.start) (x : ℂ)
    (on_bank : x ∈ Q.carrier) (not_source : x ≠ Q.start) (cone : Set ℂ)
    (radial : ∀ (v : ℂ) (r : ℝ), 0 < r → (r • v ∈ cone ↔ v ∈ cone))
    (near : ∀ᶠ z in 𝓝 x,
      z ∈ R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase ↔
        z - x ∈ cone) : frontier cone = Q.complexCarrierGerm x := by
  have outside : x ∉ R.carrier := by
    intro first
    have both : x ∈ R.carrier ∩ Q.carrier := ⟨first, on_bank⟩
    rw [R.twoBank_carriers_inter Q first_outward first_nonzero last_outward last_nonzero
      positive_phase common] at both
    exact not_source ((Set.mem_singleton_iff.mp both).trans common.symm)
  rw [R.frontier_twoBankGap_cone Q first_outward first_nonzero last_outward last_nonzero
    positive_phase common x cone radial near,
    (R.complexCarrierGerm_eq_empty_iff x).mpr outside, Set.empty_union]

/-- The actual intrinsic gap point on its second physical bank. -/
def twoBankSecondBankPoint (common : Q.start = R.start) (r : ℝ≥0) :
    PolygonalPoint
      (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase) := by
  have boundary : Q.radialPoint last_outward last_nonzero r ∈ frontier
      (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase) := by
    rw [R.frontier_twoBankGap Q first_outward first_nonzero last_outward last_nonzero
      positive_phase common]
    exact Or.inr (Q.radialPoint_mem last_outward last_nonzero r)
  exact ⟨Q.radialPoint last_outward last_nonzero r,
    (R.isClosed_twoBankGap Q first_outward first_nonzero last_outward last_nonzero
      positive_phase).closure_eq ▸ boundary.1⟩

/-- Actual incident bank rays and the original source-circle normal determine the occupied
geometric sector and its whole intrinsic metric chart. No corner aperture model is assumed. -/
theorem exists_second_bank_sector_chart (common : Q.start = R.start) (r : ℝ≥0) (radius : 0 < r)
    (frame : ℂ ≃ₗᵢ[ℝ] ℂ) (width : ℝ) (positive : 0 < width) (small : width < 2 * Real.pi)
    (banks : Q.complexCarrierGerm (Q.radialPoint last_outward last_nonzero r) =
      frame '' (Set.range (fun t : ℝ≥0 => (t : ℂ)) ∪
        Set.range (fun t : ℝ≥0 => (t : ℂ) * polarRay width)))
    (normal : -(Complex.I * (Q.radialPoint last_outward last_nonzero r - Q.start)) ∈
      interior (frame '' closedAngularSector width)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ A : Metric.eball
      (R.twoBankSecondBankPoint Q first_outward first_nonzero last_outward last_nonzero
        positive_phase common r) (ENNReal.ofReal δ) ≃ᵢ
      Metric.eball (bisectedSectorFan width positive small).origin (ENNReal.ofReal δ),
      ∀ y, Q.radialPoint last_outward last_nonzero r +
        frame ((bisectedSectorFan width positive small).develop (A y).val) = y.val.val := by
  let p := Q.radialPoint last_outward last_nonzero r
  let x := R.twoBankSecondBankPoint Q first_outward first_nonzero last_outward last_nonzero
    positive_phase common r
  obtain ⟨S, finite, cover⟩ := R.exists_twoBankGap_chamber_cover Q first_outward first_nonzero
    last_outward last_nonzero positive_phase common
  let cone := AffineArrangement.regionGerm (fun _ : S => R.bankEquation Q) (fun σ => σ.val) p
  have radial (v : ℂ) (t : ℝ) (tpos : 0 < t) : t • v ∈ cone ↔ v ∈ cone := by
    simp only [cone, AffineArrangement.regionGerm, Set.mem_iUnion,
      AffineArrangement.mem_cellGerm_smul_iff _ _ _ _ tpos]
  have near := R.eventually_mem_twoBankGap_iff_regionGerm Q first_outward first_nonzero
    last_outward last_nonzero positive_phase S finite cover p
  have not_source : p ≠ Q.start := by
    apply sub_ne_zero.mp
    apply norm_pos_iff.mp
    rw [Q.norm_radialPoint_sub_start]
    exact radius
  have boundary := R.frontier_twoBankGap_cone_at_second_bank Q first_outward first_nonzero
    last_outward last_nonzero positive_phase common p
    (Q.radialPoint_mem last_outward last_nonzero r) not_source cone radial near
  rw [banks] at boundary
  have samples := R.frequently_second_bank_interior_sector Q first_outward first_nonzero
    last_outward last_nonzero positive_phase common r radius (frame '' closedAngularSector width)
    (fun v _t tpos => mem_rotatedAngularSector_smul_iff frame width v tpos) normal
  have recognized := local_cone_eq_rotated_sector_of_frequent_witness p frame width positive small
    (R.twoBankGap_regular_closed Q first_outward first_nonzero last_outward last_nonzero
      positive_phase) radial near boundary samples
  change cone = frame '' closedAngularSector width at recognized
  change ∀ᶠ z in 𝓝 p,
    z ∈ R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase ↔
      z - p ∈ cone at near
  rw [recognized] at near
  obtain ⟨δ, δpos, local_eq⟩ := Metric.mem_nhds_iff.mp near
  let motion := frame.toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ ℂ p)
  have at_center : motion 0 = x.val := by
    change p + frame 0 = p
    rw [map_zero, add_zero]
  have local_sector (z : ℂ) (close : dist z x.val < δ) :
      z ∈ R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase ↔
        z ∈ rigidAngularSector motion width := by
    have matching :
        z ∈ R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase ↔
          z - p ∈ frame '' closedAngularSector width := local_eq (Metric.mem_ball.mpr close)
    rw [matching]
    constructor
    · rintro ⟨w, member, equal⟩
      refine ⟨w, member, ?_⟩
      change p + frame w = z
      rw [equal, add_sub_cancel]
    · rintro ⟨w, member, equal⟩
      refine ⟨w, member, ?_⟩
      change p + frame w = z at equal
      rw [← equal, add_sub_cancel_left]
  obtain ⟨A, physical⟩ := exists_reentrant_corner_fan_isometry x motion at_center width
    positive small δpos local_sector
  exact ⟨δ / 4, div_pos δpos (by norm_num), A, physical⟩

end Unfoldings.PolygonalRay
