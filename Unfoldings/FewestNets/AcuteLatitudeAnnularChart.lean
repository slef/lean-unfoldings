module

public import Unfoldings.FewestNets.AcuteLatitudeChordPairing
public import Unfoldings.Geometry.GnomonicChordTriangle
public import Unfoldings.Geometry.GnomonicRadius

/-! Each actual annular chord triangle is exactly one bounded planar normal selector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real Cap Module InnerProductGeometry

/-- Center the chart at the actual base midpoint meridian of this advance. -/
def annularChartLongitude (a : ℝ) : AnnularTriangle a → ℝ
  | ⟨j, i⟩ =>
    match sweepOrder (rowSize a j.val) (rowSize a (j.val + 1)) i with
    | .inl b => rowMidpoint (rowSize a j.val) b
    | .inr b => rowMidpoint (rowSize a (j.val + 1)) b

/-- The exact midpoint chart frame of this annular triangle. -/
def annularChartFrame (a : ℝ) (i : AnnularTriangle a) : Space ≃ₗᵢ[ℝ] Space :=
  latitudeFrame (chartColatitude a i.1.val) (annularChartLongitude a i)

/-- Each site is the actual cyclic vertex on one of the two nearby rows. -/
theorem annularVertex_offset {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (face : AnnularTriangle a) (vertex : Fin 3) :
    ∃ (row : ℕ) (w : ℝ), (row = face.1.val ∨ row = face.1.val + 1) ∧
      |w| ≤ longitudeStep a row / 2 ∧
      annularVertices a face vertex =
        latitudeSite (colatitude a row) (annularChartLongitude a face + w) := by
  obtain ⟨j, i⟩ := face
  let pass := sweepOrder (rowSize a j.val) (rowSize a (j.val + 1))
  let lon := annularChartLongitude a ⟨j, i⟩
  have represented (row n : ℕ) (which : row = j.val ∨ row = j.val + 1)
      (near : |lon - rowLongitude (rowSize a row) n| ≤ π / (rowSize a row : ℝ)) :
      ∃ w : ℝ, (row = j.val ∨ row = j.val + 1) ∧ |w| ≤ longitudeStep a row / 2 ∧
        rowSite a row n = latitudeSite (colatitude a row) (lon + w) := by
    refine ⟨rowLongitude (rowSize a row) n - lon, which, ?_, ?_⟩
    · rw [abs_sub_comm, show longitudeStep a row / 2 = π / (rowSize a row : ℝ) by
        unfold longitudeStep
        ring]
      exact near
    · unfold rowSite
      congr 1
      ring
  have sorted := sweepOrder_sorted (rowSize a j.val) (rowSize a (j.val + 1))
  have finish (row n : ℕ) (which : row = j.val ∨ row = j.val + 1)
      (sites : annularVertices a ⟨j, i⟩ vertex = rowSite a row n)
      (near : |lon - rowLongitude (rowSize a row) n| ≤ π / (rowSize a row : ℝ)) :
      ∃ (row : ℕ) (w : ℝ), (row = j.val ∨ row = j.val + 1) ∧
        |w| ≤ longitudeStep a row / 2 ∧ annularVertices a ⟨j, i⟩ vertex =
          latitudeSite (colatitude a row) (lon + w) := by
    obtain ⟨w, h, hd, p⟩ := represented row n which near
    exact ⟨row, w, h, hd, sites.trans p⟩
  rcases advance : pass i with b | b
  · have at_lon : lon = rowMidpoint (rowSize a j.val) b := by
      unfold lon
      rw [annularChartLongitude]
      rw [show sweepOrder (rowSize a j.val) (rowSize a (j.val + 1)) i = .inl b from advance]
    have sites : annularVertices a ⟨j, i⟩ = ![rowSite a j.val b.val, rowSite a j.val (b.val + 1),
        rowSite a (j.val + 1) (rowProgress (upperRank pass) i.val)] := by
      change latitudeSweepChordVertices a j.val pass i = _
      rw [latitudeSweepChordVertices, advance]
      rfl
    fin_cases vertex
    · exact finish _ _ (Or.inl rfl) (congrFun sites 0)
        (by rw [at_lon]; exact rowMidpoint_closest_left b)
    · exact finish _ _ (Or.inl rfl) (congrFun sites 1) (by
        rw [at_lon, abs_sub_comm, rowLongitude_succ_sub_rowMidpoint, abs_of_nonneg (by positivity)])
    · exact finish _ _ (Or.inr rfl) (congrFun sites 2) (by
        rw [at_lon]
        exact upperSweep_near_lower_midpoint pass sorted
          (rowSize_pos positive small (Nat.succ_le_of_lt j.isLt)) i b advance)
  · have at_lon : lon = rowMidpoint (rowSize a (j.val + 1)) b := by
      unfold lon
      rw [annularChartLongitude]
      rw [show sweepOrder (rowSize a j.val) (rowSize a (j.val + 1)) i = .inr b from advance]
    have sites : annularVertices a ⟨j, i⟩ = ![rowSite a (j.val + 1) (b.val + 1),
        rowSite a (j.val + 1) b.val, rowSite a j.val (rowProgress (lowerRank pass) i.val)] := by
      change latitudeSweepChordVertices a j.val pass i = _
      rw [latitudeSweepChordVertices, advance]
      rfl
    fin_cases vertex
    · exact finish _ _ (Or.inr rfl) (congrFun sites 0) (by
        rw [at_lon, abs_sub_comm, rowLongitude_succ_sub_rowMidpoint, abs_of_nonneg (by positivity)])
    · exact finish _ _ (Or.inr rfl) (congrFun sites 1)
        (by rw [at_lon]; exact rowMidpoint_closest_left b)
    · exact finish _ _ (Or.inl rfl) (congrFun sites 2) (by
        rw [at_lon]
        exact lowerSweep_near_upper_midpoint pass sorted
          (rowSize_pos positive small j.isLt.le) i b advance)

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

/-- The actual chord basis after rotation to its annular chart. -/
def annularChartBasis (i : AnnularTriangle a) : Basis (Fin 3) ℝ Space :=
  (chordBasis positive small (.inr (.inl i))).map (annularChartFrame a i).toLinearEquiv

@[simp] theorem annularChartBasis_apply (i : AnnularTriangle a) (j : Fin 3) :
    annularChartBasis positive small i j = annularChartFrame a i (annularVertices a i j) := by
  rw [annularChartBasis, Basis.map_apply, chordBasis_apply]
  rfl

/-- Every annular site has the paper's positive gnomonic denominator. -/
theorem annularChartBasis_height (i : AnnularTriangle a) (k : Fin 3) :
    0.991 < annularChartBasis positive small i k 2 := by
  obtain ⟨row, w, which, near, site⟩ := annularVertex_offset positive small i k
  rw [annularChartBasis_apply, site, annularChartFrame, latitudeFrame_site]
  exact (chartSite_bounds positive small i.1.isLt which (annularChartLongitude a i) w near).1

/-- The actual annular planar selector consists of the three projected sites. -/
def annularSlopeSelector (i : AnnularTriangle a) : Set Plane :=
  convexHull ℝ (Set.range (chordChartVertex (annularChartBasis positive small i)))

/-- The annular spherical patch is exactly the original chord triangle. -/
theorem annularSlopeSelector_eq_chord (i : AnnularTriangle a) :
    annularChartFrame a i ⁻¹' (gnomonicNormal '' annularSlopeSelector positive small i) =
      {p : Space | ‖p‖ = 1 ∧ ∀ j, 0 ≤ (chordBasis positive small (.inr (.inl i))).coord j p} := by
  unfold annularSlopeSelector
  rw [gnomonicNormal_image_chordChart _ (fun j =>
      (by norm_num : (0 : ℝ) < 0.991).trans (annularChartBasis_height positive small i j))]
  ext p
  change (‖annularChartFrame a i p‖ = 1 ∧ ∀ j,
    0 ≤ (annularChartBasis positive small i).coord j (annularChartFrame a i p)) ↔ _
  rw [(annularChartFrame a i).norm_map]
  have repr_eq : (annularChartBasis positive small i).repr (annularChartFrame a i p) =
      (chordBasis positive small (.inr (.inl i))).repr p := by
    rw [annularChartBasis, Basis.map_repr, LinearEquiv.trans_apply]
    exact congrArg _ ((annularChartFrame a i).toLinearEquiv.symm_apply_apply p)
  simp only [Basis.coord_apply, repr_eq, Set.mem_ofPred_eq]

private theorem annularChartVertex_norm (i : AnnularTriangle a) (k : Fin 3) :
    ‖chordChartVertex (annularChartBasis positive small i) k‖ ≤ tan (0.568 * radius a) := by
  let ell := chartColatitude a i.1.val
  let lon := annularChartLongitude a i
  let center := latitudeSite ell lon
  let vertex := annularVertices a i k
  let θ := angle center vertex
  let x := annularChartBasis positive small i k
  have angle_small : θ < 0.568 * radius a := by
    obtain ⟨row, w, which, near, site⟩ := annularVertex_offset positive small i k
    change angle center (annularVertices a i k) < _
    rw [site]
    exact (chartSite_bounds positive small i.1.isLt which lon w near).2.2.2.2.2
  have tilt_small : 0.568 * radius a < π / 2 := by
    linarith only [radius_lt small, pi_gt_d2]
  have height : x 2 = cos θ := by
    change annularChartBasis positive small i k 2 = _
    rw [annularChartBasis_apply, annularChartFrame, latitudeFrame_coordinate]
    change inner ℝ center vertex = cos (angle center vertex)
    exact inner_eq_cos_angle_of_norm_eq_one (latitudeSite_unit _ _) (annularVertices_unit a i k)
  have unit : ‖x‖ = 1 := by
    change ‖annularChartBasis positive small i k‖ = 1
    rw [annularChartBasis_apply, (annularChartFrame a i).norm_map, annularVertices_unit]
  have sine : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi (angle_nonneg _ _) (angle_le_pi _ _)
  have norm_xy : ‖horizontal x‖ = sin θ := by
    apply (sq_eq_sq₀ (norm_nonneg _) sine).mp
    have h := horizontal_norm_sq x
    rw [unit, height] at h
    linarith only [h, sin_sq_add_cos_sq θ]
  have cosine : 0 < cos θ := by
    rw [← height]
    exact (by norm_num : (0 : ℝ) < 0.991).trans (annularChartBasis_height positive small i k)
  change ‖(x 2)⁻¹ • horizontal x‖ ≤ _
  rw [norm_smul, height, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr cosine), norm_xy,
    ← div_eq_inv_mul, ← tan_eq_sin_div_cos]
  apply strictMonoOn_tan.monotoneOn
    ⟨by linarith only [angle_nonneg center vertex, pi_pos], angle_small.trans tilt_small⟩
    ⟨by linarith only [radius_pos positive, pi_pos], tilt_small⟩ angle_small.le

/-- The entire planar annular selector fits in the verified angular chart radius. -/
theorem annularSlopeSelector_radius (i : AnnularTriangle a) (p : Plane)
    (member : p ∈ annularSlopeSelector positive small i) :
    ‖p‖ ≤ tan (0.568 * radius a) := by
  have h : annularSlopeSelector positive small i ⊆ Metric.closedBall 0 (tan (0.568 * radius a)) :=
    convexHull_min (by rintro _ ⟨k, rfl⟩; simpa using annularChartVertex_norm positive small i k)
      (convex_closedBall _ _)
  simpa only [Metric.mem_closedBall, dist_zero_right] using h member

end Unfoldings.FewestNets.AcuteLatitudeGrid
