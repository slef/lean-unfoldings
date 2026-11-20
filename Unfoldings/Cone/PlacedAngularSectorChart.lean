module

public import Unfoldings.Cone.AngularSectorCycle
public import Unfoldings.Cone.DirectedIntervalChart
public import Unfoldings.Cone.ReentrantCornerChart
public import Unfoldings.Cone.SectorReflection
public import Unfoldings.Cone.SectorCoverRadius
public import Unfoldings.Metric.CenteredBallRestriction

/-! Rotate and optionally reverse whole sector charts without losing their arclength rays. -/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace Unfoldings

theorem sectorFlip_polar (width θ : ℝ) (r : ℝ≥0) :
    sectorFlip width ((r : ℂ) * polarRay θ) = (r : ℂ) * polarRay (width - θ) := by
  have reverse : starRingEnd ℂ (polarRay θ) = polarRay (-θ) := by
    have nonzero : polarRay θ ≠ 0 := fun eq => by
      have unit := norm_polarRay θ
      simp [eq] at unit
    apply mul_left_cancel₀ nonzero
    rw [polarRay_mul_conj, ← polarRay_add, add_neg_cancel, polarRay_zero]
  rw [sectorFlip_apply, map_mul, reverse, sub_eq_add_neg, polarRay_add]
  simp only [Complex.conj_ofReal]
  ring

private theorem sectorFlip_mem_closedAngularSector (width : ℝ) {z : ℂ}
    (member : z ∈ closedAngularSector width) :
    sectorFlip width z ∈ closedAngularSector width := by
  obtain ⟨r, θ, bounds, rfl⟩ := member
  exact ⟨r, width - θ, ⟨sub_nonneg.mpr bounds.2, sub_le_self _ bounds.1⟩,
    sectorFlip_polar width θ r⟩

theorem sectorFlip_image_closedAngularSector (width : ℝ) :
    sectorFlip width '' closedAngularSector width = closedAngularSector width := by
  ext z
  constructor
  · rintro ⟨w, member, rfl⟩
    exact sectorFlip_mem_closedAngularSector width member
  · intro member
    exact ⟨sectorFlip width z, sectorFlip_mem_closedAngularSector width member,
      sectorFlip_involutive width z⟩

variable {n : ℕ} (heading : Fin (n + 2) → ℝ) (i : Fin (n + 1)) (reverse : Bool)

local notation "Start" => heading i.castSucc
local notation "Width" => heading i.succ - heading i.castSucc

/-- The intrinsic sector isometry used to place a normalized chart in its cyclic position. -/
def placeAngularSector : PolygonalPoint (closedAngularSector Width) ≃ᵢ
    PolygonalPoint (placedAngularSector heading i) :=
  let R := rotation (Circle.exp Start)
  let turn := PolygonalPoint.affineRegionIsometryEquiv R.toAffineIsometryEquiv (t := placedAngularSector heading i) rfl
  if reverse then
    (PolygonalPoint.affineRegionIsometryEquiv (sectorFlip Width).toAffineIsometryEquiv
      (sectorFlip_image_closedAngularSector Width).symm).trans turn
  else turn

theorem placeAngularSector_val (x : PolygonalPoint (closedAngularSector Width)) :
    (placeAngularSector heading i reverse x).val =
      rotation (Circle.exp Start) (if reverse then sectorFlip Width x.val else x.val) := by
  cases reverse <;> rfl

/-- The apex can be chosen once for both orientations of the chart. -/
def placedAngularOrigin (nonneg : 0 ≤ Width) : PolygonalPoint (placedAngularSector heading i) :=
  placeAngularSector heading i false (closedAngularSectorOrigin nonneg)

@[simp] theorem placedAngularOrigin_val (nonneg : 0 ≤ Width) :
    (placedAngularOrigin heading i nonneg).val = 0 := by
  simp [placedAngularOrigin, placeAngularSector_val, closedAngularSectorOrigin]

theorem placeAngularSector_center (nonneg : 0 ≤ Width) :
    placeAngularSector heading i reverse (closedAngularSectorOrigin nonneg) =
      placedAngularOrigin heading i nonneg := by
  apply PolygonalPoint.ext
  rw [placeAngularSector_val, placedAngularOrigin_val]
  cases reverse <;> simp [closedAngularSectorOrigin]

theorem placedAngularOrigin_radial (nonneg : 0 ≤ Width)
    (z : PolygonalPoint (placedAngularSector heading i)) :
    edist z (placedAngularOrigin heading i nonneg) = edist z.val (0 : ℂ) := by
  have star : StarConvex ℝ (0 : ℂ) (placedAngularSector heading i) := by
    let R := rotation (Circle.exp Start)
    have h := (starConvex_closedAngularSector Width).linear_image R.toLinearMap
    change StarConvex ℝ (R 0) (placedAngularSector heading i) at h
    rw [map_zero] at h
    exact h
  rw [edist_comm z, edist_comm z.val]
  have segment_inside : segment ℝ (placedAngularOrigin heading i nonneg).val z.val ⊆
      placedAngularSector heading i := by
    rw [placedAngularOrigin_val]
    exact star.segment_subset z.property
  exact (PolygonalPoint.edist_eq_of_segment segment_inside).trans
    (congrArg (edist · z.val) (placedAngularOrigin_val heading i nonneg))

theorem placeAngularSector_polar (x : PolygonalPoint (closedAngularSector Width))
    (r : ℝ≥0) (φ : ℝ) (at_ray : x.val = (r : ℂ) * polarRay φ) :
    (placeAngularSector heading i reverse x).val =
      (r : ℂ) * polarRay (Start + if reverse then Width - φ else φ) := by
  rw [placeAngularSector_val, at_ray]
  cases reverse
  · simpa only [Bool.false_eq_true, ite_false] using rotate_polar_point Start φ r
  · simp only [ite_true, sectorFlip_polar]
    exact rotate_polar_point Start (Width - φ) r

/-- Placement sends the selected normalized bank to the exact starting or
finishing heading, with the same scalar radius. -/
theorem placeAngularSector_bankRay (x : PolygonalPoint (closedAngularSector Width))
    (terminal : Bool) {d : ℝ} (nonnegative : 0 ≤ d)
    (bank : x.val = d • polarRay (if terminal then Width else 0)) :
    (placeAngularSector heading i reverse x).val =
      d • polarRay (if terminal = reverse then Start else heading i.succ) := by
  let r : ℝ≥0 := ⟨d, nonnegative⟩
  have placed := placeAngularSector_polar heading i reverse x r
    (if terminal then Width else 0) (by
      change x.val = (d : ℂ) * polarRay (if terminal then Width else 0)
      simpa only [Complex.real_smul] using bank)
  rw [placed, Complex.real_smul]
  congr 2
  cases reverse <;> cases terminal <;> simp <;> ring

variable {X : Type*} [EMetricSpace X] (x : X) (nonneg : 0 ≤ heading i.succ - heading i.castSucc) {r R : ℝ≥0∞}
  (positive : 0 < R) (small : r ≤ R)
  (chart : Metric.eball x R ≃ᵢ Metric.eball (closedAngularSectorOrigin nonneg) R)
  (center : (chart ⟨x, Metric.mem_eball_self positive⟩).val = closedAngularSectorOrigin nonneg)

/-- Restrict an original whole sector chart to the common radius and place it. -/
def placeCenteredSectorChart :
    Metric.eball x r ≃ᵢ Metric.eball (placedAngularOrigin heading i nonneg) r :=
  (restrictCenteredEBallEquiv positive small chart center).trans
    (basedEBallIsometry (placeAngularSector heading i reverse) (closedAngularSectorOrigin nonneg)
      (placedAngularOrigin heading i nonneg) (placeAngularSector_center heading i reverse nonneg) r)

@[simp] theorem placeCenteredSectorChart_val (y : Metric.eball x r) :
    (placeCenteredSectorChart heading i reverse x nonneg positive small chart center y).val =
      placeAngularSector heading i reverse (chart ⟨y.val, y.property.trans_le small⟩).val := by
  rw [placeCenteredSectorChart, IsometryEquiv.trans_apply, basedEBallIsometry_apply,
    restrictCenteredEBallEquiv_val]

theorem placeCenteredSectorChart_center (rpos : 0 < r) :
    (placeCenteredSectorChart heading i reverse x nonneg positive small chart center
      ⟨x, Metric.mem_eball_self rpos⟩).val = placedAngularOrigin heading i nonneg := by
  rw [placeCenteredSectorChart_val]
  exact (congrArg (placeAngularSector heading i reverse) center).trans
    (placeAngularSector_center heading i reverse nonneg)

theorem placeCenteredSectorChart_bankRay (y : Metric.eball x r)
    (terminal : Bool) {d : ℝ} (nonnegative : 0 ≤ d)
    (bank : (chart ⟨y.val, y.property.trans_le small⟩).val.val =
      d • polarRay (if terminal then Width else 0)) :
    (placeCenteredSectorChart heading i reverse x nonneg positive small chart center y).val.val =
      d • polarRay (if terminal = reverse then Start else heading i.succ) := by
  rw [placeCenteredSectorChart_val]
  exact placeAngularSector_bankRay heading i reverse _ terminal nonnegative bank

section
variable {Z : Type*} [EMetricSpace Z]

/-- A normalized whole sector centered at an original point, before cyclic placement. -/
structure CenteredSectorGerm (z : Z) (angle : ℝ) where
  angle_pos : 0 < angle
  radius : ℝ
  radius_pos : 0 < radius
  chart : Metric.eball z (ENNReal.ofReal radius) ≃ᵢ
    Metric.eball (closedAngularSectorOrigin angle_pos.le) (ENNReal.ofReal radius)
  centered : (chart ⟨z, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr radius_pos)⟩).val =
    closedAngularSectorOrigin angle_pos.le

end

namespace MetricGluing.SectorCoverChart

variable {I : Type*} (Y : I → Type*) [∀ j, EMetricSpace (Y j)]
  (places : Fin (n + 2) → ℝ) (centers : Fin (n + 1) → Total Y)
  (flip : Fin (n + 1) → Bool)
  (nonnegative : ∀ j : Fin (n + 1), 0 ≤ places j.succ - places j.castSucc)
  (radius : Fin (n + 1) → ℝ) (radius_pos : ∀ j, 0 < radius j)
  (localChart : ∀ j, Metric.eball (centers j).2 (ENNReal.ofReal (radius j)) ≃ᵢ
    Metric.eball (closedAngularSectorOrigin (nonnegative j)) (ENNReal.ofReal (radius j)))
  (at_center : ∀ j, (localChart j ⟨(centers j).2,
    Metric.mem_eball_self (ENNReal.ofReal_pos.mpr (radius_pos j))⟩).val =
      closedAngularSectorOrigin (nonnegative j))

/-- Restrict the normalized charts to a common radius and place them in their cyclic order. -/
def ofCenteredSectors {ρ : ℝ} (positive : 0 < ρ) (small : ∀ j, ρ ≤ radius j)
    (separated : ∀ (j k : Fin (n + 1)), j ≠ k →
      ∀ (tag : (centers j).1 = (centers k).1)
        (x : Metric.eball (centers j).2 (ENNReal.ofReal ρ))
        (y : Metric.eball (centers k).2 (ENNReal.ofReal ρ)),
        ENNReal.ofReal (2 * ρ) ≤ edist (tag ▸ x.val) y.val) :
    SectorCoverChart Y centers (placedAngularSector places)
      (fun j => placedAngularOrigin places j (nonnegative j)) ρ where
  positive := positive
  chart j := placeCenteredSectorChart places j (flip j) (centers j).2 (nonnegative j)
    (ENNReal.ofReal_pos.mpr (radius_pos j)) (ENNReal.ofReal_le_ofReal (small j))
    (localChart j) (at_center j)
  centered j := placeCenteredSectorChart_center places j (flip j) (centers j).2
    (nonnegative j) (ENNReal.ofReal_pos.mpr (radius_pos j))
    (ENNReal.ofReal_le_ofReal (small j)) (localChart j) (at_center j)
    (ENNReal.ofReal_pos.mpr positive)
  radial j := placedAngularOrigin_radial places j (nonnegative j)
  separated := separated

section CommonRadius
variable {ι : Type*} (E : ι → Type*) [∀ i, EMetricSpace (E i)]
  (headings : Fin (n + 2) → ℝ) (centers' : Fin (n + 1) → Total E)
  (flipped : Fin (n + 1) → Bool)
  (germs : ∀ j : Fin (n + 1), CenteredSectorGerm (centers' j).2
    (headings j.succ - headings j.castSucc))

include flipped in
/-- An injective finite family of centered original charts admits a common
placed radius below any prescribed positive clearance. -/
theorem exists_of_centered_sectors (distinct : Function.Injective centers')
    {limit : ℝ} (bound_pos : 0 < limit) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ limit ∧
      Nonempty (SectorCoverChart E centers' (placedAngularSector headings)
        (fun j => placedAngularOrigin headings j (germs j).angle_pos.le) ρ) := by
  obtain ⟨sep, sep_pos, separated⟩ := exists_sectorCover_separationRadius E centers' distinct
  obtain ⟨rad, rad_pos, radii⟩ := MetricBarrier.exists_pos_le_of_finite
    (fun j => (germs j).radius) (fun j => (germs j).radius_pos)
  let ρ := min limit (min sep rad)
  have positive : 0 < ρ := lt_min bound_pos (lt_min sep_pos rad_pos)
  have sep_small : ρ ≤ sep := (min_le_right _ _).trans (min_le_left _ _)
  have rad_small (j : Fin (n + 1)) : ρ ≤ (germs j).radius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (radii j))
  let placed := ofCenteredSectors E headings centers' flipped (fun j => (germs j).angle_pos.le)
    (fun j => (germs j).radius) (fun j => (germs j).radius_pos)
    (fun j => (germs j).chart) (fun j => (germs j).centered) positive rad_small
    (separated ρ positive sep_small)
  exact ⟨ρ, positive, min_le_left _ _, ⟨placed⟩⟩

end CommonRadius

end MetricGluing.SectorCoverChart

end Unfoldings
