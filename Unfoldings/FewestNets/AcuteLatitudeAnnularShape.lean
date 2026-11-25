module

public import Unfoldings.FewestNets.AcuteLatitudeAnnularChart
public import Unfoldings.FewestNets.AcuteLatitudeRouting

/-! The actual midpoint triangles have the literal symmetric bases and signed heights used for routing. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real Cap

/-- The exact slope coordinates of a site at a specified offset. -/
def annularSlopePoint (a : ℝ) (strip row : ℕ) (w : ℝ) : Plane :=
  WithLp.toLp 2 ![chartX (chartColatitude a strip) (colatitude a row) w,
    chartY (chartColatitude a strip) (colatitude a row) w]

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

private theorem annularChartVertex_at (i : AnnularTriangle a) (vertex : Fin 3) (row : ℕ) (w : ℝ)
    (site : annularVertices a i vertex =
      latitudeSite (colatitude a row) (annularChartLongitude a i + w)) :
    chordChartVertex (annularChartBasis positive small i) vertex =
      annularSlopePoint a i.1.val row w := by
  rw [chordChartVertex, annularChartBasis_apply, site, annularChartFrame]
  exact latitude_gnomonic_site _ _ _ _

/-- The actual annular selector has symmetric base offsets and the prescribed nearest-row apex. -/
theorem exists_annularSlopeSelector_base (i : AnnularTriangle a) :
    ∃ (baseRow apexRow : ℕ) (w : ℝ),
      ((baseRow = i.1.val ∧ apexRow = i.1.val + 1) ∨
        (baseRow = i.1.val + 1 ∧ apexRow = i.1.val)) ∧
      |w| ≤ longitudeStep a apexRow / 2 ∧
      annularSlopeSelector positive small i = convexHull ℝ
        {annularSlopePoint a i.1.val baseRow (-(longitudeStep a baseRow / 2)),
          annularSlopePoint a i.1.val baseRow (longitudeStep a baseRow / 2),
          annularSlopePoint a i.1.val apexRow w} := by
  obtain ⟨j, i⟩ := i
  let step := sweepOrder (rowSize a j.val) (rowSize a (j.val + 1))
  let u := annularChartLongitude a ⟨j, i⟩
  let vertex := chordChartVertex (annularChartBasis positive small ⟨j, i⟩)
  have base_first {row : ℕ} (b : Fin (rowSize a row)) (mid : u = rowMidpoint (rowSize a row) b) :
      rowSite a row b.val = latitudeSite (colatitude a row) (u - longitudeStep a row / 2) := by
    unfold rowSite
    rw [mid]
    congr 1
    unfold longitudeStep
    linarith only [rowMidpoint_sub_rowLongitude b,
      show (2 * π) / (rowSize a row : ℝ) / 2 = π / (rowSize a row : ℝ) by ring]
  have base_last {row : ℕ} (b : Fin (rowSize a row)) (mid : u = rowMidpoint (rowSize a row) b) :
      rowSite a row (b.val + 1) = latitudeSite (colatitude a row) (u + longitudeStep a row / 2) := by
    unfold rowSite
    rw [mid]
    congr 1
    unfold longitudeStep
    linarith only [rowLongitude_succ_sub_rowMidpoint b,
      show (2 * π) / (rowSize a row : ℝ) / 2 = π / (rowSize a row : ℝ) by ring]
  have apex (row n : ℕ) :
      let w := rowLongitude (rowSize a row) n - u
      rowSite a row n = latitudeSite (colatitude a row) (u + w) := by
    unfold rowSite
    dsimp only
    congr 1
    ring
  have half (row n : ℕ) (h : |u - rowLongitude (rowSize a row) n| ≤ π / (rowSize a row : ℝ)) :
      |rowLongitude (rowSize a row) n - u| ≤ longitudeStep a row / 2 := by
    rw [abs_sub_comm, show longitudeStep a row / 2 = π / (rowSize a row : ℝ) by
      unfold longitudeStep
      ring]
    exact h
  have hull (x y z : Plane) (at₀ : vertex 0 = x) (at₁ : vertex 1 = y)
      (at₂ : vertex 2 = z) :
      annularSlopeSelector positive small ⟨j, i⟩ = convexHull ℝ {x, y, z} := by
    have range : Set.range vertex = {x, y, z} := by
      ext p
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨k, rfl⟩
        fin_cases k
        · exact Or.inl at₀
        · exact Or.inr (Or.inl at₁)
        · exact Or.inr (Or.inr at₂)
      · rintro (rfl | rfl | rfl)
        · exact ⟨0, at₀⟩
        · exact ⟨1, at₁⟩
        · exact ⟨2, at₂⟩
    exact congrArg (convexHull ℝ) range
  have sorted := sweepOrder_sorted (rowSize a j.val) (rowSize a (j.val + 1))
  rcases advance : step i with b | b
  · let n := rowProgress (upperRank step) i.val
    let w := rowLongitude (rowSize a (j.val + 1)) n - u
    have mid : u = rowMidpoint (rowSize a j.val) b := by
      unfold u
      rw [annularChartLongitude]
      rw [show (sweepOrder _ _) i = .inl b from advance]
    have actual : annularVertices a ⟨j, i⟩ =
        ![rowSite a j.val b.val, rowSite a j.val (b.val + 1), rowSite a (j.val + 1) n] := by
      change latitudeSweepChordVertices a j.val step i = _
      rw [latitudeSweepChordVertices, advance]
      rfl
    refine ⟨j.val, j.val + 1, w, Or.inl ⟨rfl, rfl⟩, half _ _ ?_, ?_⟩
    · rw [mid]
      exact upperSweep_near_lower_midpoint step sorted
        (rowSize_pos positive small (Nat.succ_le_of_lt j.isLt)) i b advance
    · let x := annularSlopePoint a j.val j.val (-(longitudeStep a j.val / 2))
      let y := annularSlopePoint a j.val j.val (longitudeStep a j.val / 2)
      let z := annularSlopePoint a j.val (j.val + 1) w
      have at₀ : vertex 0 = x := annularChartVertex_at positive small _ 0 _ _
        ((congrFun actual 0).trans (base_first b mid))
      have at₁ : vertex 1 = y := annularChartVertex_at positive small _ 1 _ _
        ((congrFun actual 1).trans (base_last b mid))
      have at₂ : vertex 2 = z := annularChartVertex_at positive small _ 2 _ _
        ((congrFun actual 2).trans (apex _ _))
      exact hull x y z at₀ at₁ at₂
  · let n := rowProgress (lowerRank step) i.val
    let w := rowLongitude (rowSize a j.val) n - u
    let row := j.val + 1
    have mid : u = rowMidpoint (rowSize a row) b := by
      unfold u
      rw [annularChartLongitude]
      rw [show (sweepOrder _ _) i = .inr b from advance]
    have actual : annularVertices a ⟨j, i⟩ =
        ![rowSite a row (b.val + 1), rowSite a row b.val, rowSite a j.val n] := by
      change latitudeSweepChordVertices a j.val step i = _
      rw [latitudeSweepChordVertices, advance]
      rfl
    refine ⟨row, j.val, w, Or.inr ⟨rfl, rfl⟩, half _ _ ?_, ?_⟩
    · rw [mid]
      exact lowerSweep_near_upper_midpoint step sorted (rowSize_pos positive small j.isLt.le) i b advance
    · let x := annularSlopePoint a j.val row (-(longitudeStep a row / 2))
      let y := annularSlopePoint a j.val row (longitudeStep a row / 2)
      let z := annularSlopePoint a j.val j.val w
      have at₀ : vertex 0 = y := annularChartVertex_at positive small _ 0 _ _
        ((congrFun actual 0).trans (base_last b mid))
      have at₁ : vertex 1 = x := annularChartVertex_at positive small _ 1 _ _
        ((congrFun actual 1).trans (base_first b mid))
      have at₂ : vertex 2 = z := annularChartVertex_at positive small _ 2 _ _
        ((congrFun actual 2).trans (apex _ _))
      rw [Set.insert_comm x y]
      exact hull y x z at₀ at₁ at₂

include positive small in
/-- The two symmetric base vertices have the exact horizontal bounds at the revised scale. -/
theorem annular_chart_base_width {strip row : ℕ} (valid : strip < stripCount a)
    (which : row = strip ∨ row = strip + 1) :
    let ell := chartColatitude a strip
    let d := longitudeStep a row / 2
    0.8 * spacing a < 2 * chartX ell (colatitude a row) d ∧
      2 * chartX ell (colatitude a row) d < 1.010 * spacing a := by
  let d := longitudeStep a row / 2
  let ell := chartColatitude a strip
  have row_valid : row ≤ stripCount a := by rcases which with rfl | rfl <;> omega
  have d_pos : 0 < d := div_pos (longitudeStep_pos_lt_pi positive small row_valid).1 (by norm_num)
  have h := chartSite_bounds positive small valid which 0 d (abs_of_pos d_pos).le
  have sine := row_sine_lower positive small row_valid
  have sine' : (0.999 / 3.864) * radius a < sin (colatitude a row) := by
    rw [radius_eq_polarRadius]
    linarith only [sine]
  have wide := longitudeStep_bounds positive small row_valid
  have width := chart_base_bounds (radius_pos positive) (spacing_pos positive) (spacing_lt positive small)
    sine' h.1 h.2.1 wide.1 wide.2
  change 0.8 * spacing a < 2 * chartX ell (colatitude a row) d ∧
    2 * chartX ell (colatitude a row) d < 1.010 * spacing a
  have exact_width : 2 * chartX ell (colatitude a row) d =
      2 * sin (colatitude a row) * sin d / latitudeDenominator ell (colatitude a row) d := by
    unfold chartX
    rw [← mul_div_assoc]
    ring
  rw [exact_width]
  simpa only [d, ell] using width

end Unfoldings.FewestNets.AcuteLatitudeGrid
