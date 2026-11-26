module

public import Unfoldings.FewestNets.RevisedLatitudeOrientation
public import Unfoldings.Geometry.GnomonicChordTriangle
public import Unfoldings.Geometry.GnomonicRadius

/-! Each actual annular chord triangle is exactly one bounded planar normal selector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real Cap Module InnerProductGeometry

open LatitudeRings (sweepOrder sweepOrder_sorted latitudeSweepChordVertices latitudeSweepCrossSites)

abbrev AnnularTriangle (a : ℝ) := (rings a).AnnularTriangle

/-- Center the chart at the actual base midpoint meridian of this advance. -/
def annularChartLongitude (a : ℝ) : AnnularTriangle a → ℝ
  | ⟨j, i⟩ =>
    match sweepOrder (rowSize a j.val) (rowSize a (j.val + 1)) i with
    | .inl b => rowMidpoint (rowSize a j.val) b
    | .inr b => rowMidpoint (rowSize a (j.val + 1)) b

/-- The exact midpoint chart frame of this annular triangle. -/
def annularChartFrame (a : ℝ) (i : AnnularTriangle a) : Space ≃ₗᵢ[ℝ] Space :=
  latitudeFrame (stripMidpoint a i.1.val) (annularChartLongitude a i)

/-- Each site is the actual cyclic vertex on one of the two nearby rows. -/
theorem annularVertex_offset {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (face : AnnularTriangle a) (vertex : Fin 3) :
    ∃ (row : ℕ) (w : ℝ), (row = face.1.val ∨ row = face.1.val + 1) ∧
      |w| ≤ longitudeStep a row / 2 ∧
      (rings a).annularVertices face vertex =
        latitudeSite (colatitude a row) (annularChartLongitude a face + w) := by
  obtain ⟨j, i⟩ := face
  let pass := sweepOrder (rowSize a j.val) (rowSize a (j.val + 1))
  let lon := annularChartLongitude a ⟨j, i⟩
  have represented (row n : ℕ) (which : row = j.val ∨ row = j.val + 1)
      (near : |lon - rowLongitude (rowSize a row) n| ≤ π / (rowSize a row : ℝ)) :
      ∃ w : ℝ, (row = j.val ∨ row = j.val + 1) ∧ |w| ≤ longitudeStep a row / 2 ∧
        (rings a).rowSite row n = latitudeSite (colatitude a row) (lon + w) := by
    refine ⟨rowLongitude (rowSize a row) n - lon, which, ?_, ?_⟩
    · rw [abs_sub_comm, show longitudeStep a row / 2 = π / (rowSize a row : ℝ) by
        unfold longitudeStep
        ring]
      exact near
    · change latitudeSite (colatitude a row) (rowLongitude (rowSize a row) n) = _
      congr 1
      ring
  have sorted := sweepOrder_sorted (rowSize a j.val) (rowSize a (j.val + 1))
  have finish (row n : ℕ) (which : row = j.val ∨ row = j.val + 1)
      (sites : (rings a).annularVertices ⟨j, i⟩ vertex = (rings a).rowSite row n)
      (near : |lon - rowLongitude (rowSize a row) n| ≤ π / (rowSize a row : ℝ)) :
      ∃ (row : ℕ) (w : ℝ), (row = j.val ∨ row = j.val + 1) ∧
        |w| ≤ longitudeStep a row / 2 ∧ (rings a).annularVertices ⟨j, i⟩ vertex =
          latitudeSite (colatitude a row) (lon + w) := by
    obtain ⟨w, h, hd, p⟩ := represented row n which near
    exact ⟨row, w, h, hd, sites.trans p⟩
  rcases advance : pass i with b | b
  · have at_lon : lon = rowMidpoint (rowSize a j.val) b := by
      unfold lon
      rw [annularChartLongitude]
      rw [show sweepOrder (rowSize a j.val) (rowSize a (j.val + 1)) i = .inl b from advance]
    have sites : (rings a).annularVertices ⟨j, i⟩ = ![(rings a).rowSite j.val b.val, (rings a).rowSite j.val (b.val + 1),
        (rings a).rowSite (j.val + 1) (rowProgress (upperRank pass) i.val)] := by
      change latitudeSweepChordVertices (rings a) j.val pass i = _
      delta LatitudeRings.latitudeSweepChordVertices
      rw [advance]
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
    have sites : (rings a).annularVertices ⟨j, i⟩ = ![(rings a).rowSite (j.val + 1) (b.val + 1),
        (rings a).rowSite (j.val + 1) b.val, (rings a).rowSite j.val (rowProgress (lowerRank pass) i.val)] := by
      change latitudeSweepChordVertices (rings a) j.val pass i = _
      delta LatitudeRings.latitudeSweepChordVertices
      rw [advance]
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
  (LatitudeRings.chordBasis (rings_oriented positive small) (.inr (.inl i))).map (annularChartFrame a i).toLinearEquiv

@[simp] theorem annularChartBasis_apply (i : AnnularTriangle a) (j : Fin 3) :
    annularChartBasis positive small i j = annularChartFrame a i ((rings a).annularVertices i j) := by
  rw [annularChartBasis, Basis.map_apply, LatitudeRings.chordBasis_apply]
  rfl

/-- Every annular site has the paper's positive gnomonic denominator. -/
theorem annularChartBasis_height (i : AnnularTriangle a) (k : Fin 3) :
    0.9612 < annularChartBasis positive small i k 2 := by
  obtain ⟨row, w, which, near, site⟩ := annularVertex_offset positive small i k
  rw [annularChartBasis_apply, site, annularChartFrame, latitudeFrame_site]
  exact (slopeSite_bounds positive small i.1.isLt which near).1

/-- The actual annular planar selector consists of the three projected sites. -/
def annularSlopeSelector (i : AnnularTriangle a) : Set Plane :=
  convexHull ℝ (Set.range (chordChartVertex (annularChartBasis positive small i)))

/-- The annular spherical patch is exactly the original chord triangle. -/
theorem annularSlopeSelector_eq_chord (i : AnnularTriangle a) :
    annularChartFrame a i ⁻¹' (gnomonicNormal '' annularSlopeSelector positive small i) =
      {p : Space | ‖p‖ = 1 ∧ ∀ j, 0 ≤ (LatitudeRings.chordBasis (rings_oriented positive small) (.inr (.inl i))).coord j p} := by
  unfold annularSlopeSelector
  rw [gnomonicNormal_image_chordChart _ (fun j =>
      (by norm_num : (0 : ℝ) < 0.9612).trans (annularChartBasis_height positive small i j))]
  ext p
  change (‖annularChartFrame a i p‖ = 1 ∧ ∀ j,
    0 ≤ (annularChartBasis positive small i).coord j (annularChartFrame a i p)) ↔ _
  rw [(annularChartFrame a i).norm_map]
  have repr_eq : (annularChartBasis positive small i).repr (annularChartFrame a i p) =
      (LatitudeRings.chordBasis (rings_oriented positive small) (.inr (.inl i))).repr p := by
    rw [annularChartBasis, Basis.map_repr, LinearEquiv.trans_apply]
    exact congrArg _ ((annularChartFrame a i).toLinearEquiv.symm_apply_apply p)
  simp only [Basis.coord_apply, repr_eq, Set.mem_ofPred_eq]

end Unfoldings.FewestNets.RevisedLatitudeGrid
