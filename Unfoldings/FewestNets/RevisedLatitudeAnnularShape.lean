module

public import Unfoldings.FewestNets.RevisedLatitudeAnnularChart
public import Unfoldings.FewestNets.RevisedLatitudeBaseSampling

/-! The actual midpoint triangles have the literal symmetric bases and signed heights used for routing. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real Cap

open LatitudeRings (sweepOrder sweepOrder_sorted latitudeSweepChordVertices)

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

private theorem annularChartVertex_at (i : AnnularTriangle a) (vertex : Fin 3) (row : ℕ) (w : ℝ)
    (site : (rings a).annularVertices i vertex =
      latitudeSite (colatitude a row) (annularChartLongitude a i + w)) :
    chordChartVertex (annularChartBasis positive small i) vertex =
      slopeSite a i.1.val row w := by
  rw [chordChartVertex, annularChartBasis_apply, site, annularChartFrame]
  exact latitude_gnomonic_site _ _ _ _

/-- The exact planar vertex corresponding to one of the three ordered chord vertices. -/
def annularSlopeVertex (i : AnnularTriangle a) (j : Fin 3) : Plane :=
  chordChartVertex (annularChartBasis positive small i) j

/-- The base row and strip in the actual annular triangle. -/
def baseRow {a : ℝ} (i : AnnularTriangle a) : ℕ :=
  match LatitudeRings.sweepOrder (rowSize a i.1.val) (rowSize a (i.1.val + 1)) i.2 with
  | .inl _ => i.1.val
  | .inr _ => i.1.val + 1

/-- The actual annular selector has symmetric base offsets and the prescribed nearest-row apex. -/
theorem exists_annularSlopeSelector_base (i : AnnularTriangle a) :
    ∃ (baseRow apexRow : ℕ) (w : ℝ),
      baseRow = RevisedLatitudeGrid.baseRow i ∧
      ((baseRow = i.1.val ∧ apexRow = i.1.val + 1) ∨
        (baseRow = i.1.val + 1 ∧ apexRow = i.1.val)) ∧
      |w| ≤ longitudeStep a apexRow / 2 ∧
      annularSlopeSelector positive small i = convexHull ℝ
        {slopeSite a i.1.val baseRow (-(longitudeStep a baseRow / 2)),
          slopeSite a i.1.val baseRow (longitudeStep a baseRow / 2),
          slopeSite a i.1.val apexRow w} ∧
      let x := slopeSite a i.1.val baseRow (-(longitudeStep a baseRow / 2))
      let y := slopeSite a i.1.val baseRow (longitudeStep a baseRow / 2)
      let z := slopeSite a i.1.val apexRow w
      let v := annularSlopeVertex positive small i
      v 2 = z ∧ ((v 0 = x ∧ v 1 = y) ∨ (v 0 = y ∧ v 1 = x)) := by
  obtain ⟨j, i⟩ := i
  let step := sweepOrder (rowSize a j.val) (rowSize a (j.val + 1))
  let u := annularChartLongitude a ⟨j, i⟩
  let vertex := chordChartVertex (annularChartBasis positive small ⟨j, i⟩)
  have base_first {row : ℕ} (b : Fin (rowSize a row)) (mid : u = rowMidpoint (rowSize a row) b) :
      (rings a).rowSite row b.val = latitudeSite (colatitude a row) (u - longitudeStep a row / 2) := by
    change latitudeSite (colatitude a row) (rowLongitude (rowSize a row) _) = _
    rw [mid]
    congr 1
    unfold longitudeStep
    linarith only [rowMidpoint_sub_rowLongitude b,
      show (2 * π) / (rowSize a row : ℝ) / 2 = π / (rowSize a row : ℝ) by ring]
  have base_last {row : ℕ} (b : Fin (rowSize a row)) (mid : u = rowMidpoint (rowSize a row) b) :
      (rings a).rowSite row (b.val + 1) = latitudeSite (colatitude a row) (u + longitudeStep a row / 2) := by
    change latitudeSite (colatitude a row) (rowLongitude (rowSize a row) _) = _
    rw [mid]
    congr 1
    unfold longitudeStep
    linarith only [rowLongitude_succ_sub_rowMidpoint b,
      show (2 * π) / (rowSize a row : ℝ) / 2 = π / (rowSize a row : ℝ) by ring]
  have apex (row n : ℕ) :
      let w := rowLongitude (rowSize a row) n - u
      (rings a).rowSite row n = latitudeSite (colatitude a row) (u + w) := by
    change latitudeSite (colatitude a row) (rowLongitude (rowSize a row) _) = _
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
    have actual : (rings a).annularVertices ⟨j, i⟩ =
        ![(rings a).rowSite j.val b.val, (rings a).rowSite j.val (b.val + 1), (rings a).rowSite (j.val + 1) n] := by
      change latitudeSweepChordVertices (rings a) j.val step i = _
      delta LatitudeRings.latitudeSweepChordVertices
      rw [advance]
      rfl
    refine ⟨j.val, j.val + 1, w, ?_, Or.inl ⟨rfl, rfl⟩, half _ _ ?_, ?_⟩
    · unfold baseRow
      rw [show (sweepOrder _ _) i = _ from advance]
    · rw [mid]
      exact upperSweep_near_lower_midpoint step sorted
        (rowSize_pos positive small (Nat.succ_le_of_lt j.isLt)) i b advance
    · let x := slopeSite a j.val j.val (-(longitudeStep a j.val / 2))
      let y := slopeSite a j.val j.val (longitudeStep a j.val / 2)
      let z := slopeSite a j.val (j.val + 1) w
      have at₀ : vertex 0 = x := annularChartVertex_at positive small _ 0 _ _
        ((congrFun actual 0).trans (base_first b mid))
      have at₁ : vertex 1 = y := annularChartVertex_at positive small _ 1 _ _
        ((congrFun actual 1).trans (base_last b mid))
      have at₂ : vertex 2 = z := annularChartVertex_at positive small _ 2 _ _
        ((congrFun actual 2).trans (apex _ _))
      exact ⟨hull x y z at₀ at₁ at₂, at₂, Or.inl ⟨at₀, at₁⟩⟩
  · let n := rowProgress (lowerRank step) i.val
    let w := rowLongitude (rowSize a j.val) n - u
    let row := j.val + 1
    have mid : u = rowMidpoint (rowSize a row) b := by
      unfold u
      rw [annularChartLongitude]
      rw [show (sweepOrder _ _) i = .inr b from advance]
    have actual : (rings a).annularVertices ⟨j, i⟩ =
        ![(rings a).rowSite row (b.val + 1), (rings a).rowSite row b.val, (rings a).rowSite j.val n] := by
      change latitudeSweepChordVertices (rings a) j.val step i = _
      delta LatitudeRings.latitudeSweepChordVertices
      rw [advance]
      rfl
    refine ⟨row, j.val, w, ?_, Or.inr ⟨rfl, rfl⟩, half _ _ ?_, ?_⟩
    · unfold baseRow
      rw [show (sweepOrder _ _) i = _ from advance]
    · rw [mid]
      exact lowerSweep_near_upper_midpoint step sorted (rowSize_pos positive small j.isLt.le) i b advance
    · let x := slopeSite a j.val row (-(longitudeStep a row / 2))
      let y := slopeSite a j.val row (longitudeStep a row / 2)
      let z := slopeSite a j.val j.val w
      have at₀ : vertex 0 = y := annularChartVertex_at positive small _ 0 _ _
        ((congrFun actual 0).trans (base_last b mid))
      have at₁ : vertex 1 = x := annularChartVertex_at positive small _ 1 _ _
        ((congrFun actual 1).trans (base_first b mid))
      have at₂ : vertex 2 = z := annularChartVertex_at positive small _ 2 _ _
        ((congrFun actual 2).trans (apex _ _))
      rw [Set.insert_comm x y]
      exact ⟨hull y x z at₀ at₁ at₂, at₂, Or.inr ⟨at₀, at₁⟩⟩


include positive small in
/-- A horizontal base keeps its stronger cosine-weighted lower bound. -/
theorem annular_base_width {strip row : ℕ} (valid : strip < stripCount a)
    (which : row = strip ∨ row = strip + 1) :
    let d := longitudeStep a row / 2
    let B := 2 * (slopeSite a strip row d) 0
    (if isPolarRow a row then 0.432 else 0.952) * spacing a <
      B * cos (rowStep a / 2) ∧ B < spacing a / 0.9612 := by
  let d := longitudeStep a row / 2
  let Z := latitudeDenominator (stripMidpoint a strip) (colatitude a row) d
  let B := 2 * (slopeSite a strip row d) 0
  let raw := 2 * sin (colatitude a row) * sin d
  have row_valid : row ≤ stripCount a := by rcases which with rfl | rfl <;> omega
  have dp : 0 < d := half_pos (longitudeStep_pos_lt_pi positive small row_valid).1
  have dn : |d| ≤ longitudeStep a row / 2 := (abs_of_pos dp).le
  obtain ⟨Zl, Zu, _, _⟩ := slopeSite_bounds positive small valid which dn
  have Zp : 0 < Z := (by norm_num : (0 : ℝ) < 0.9612).trans Zl
  have c : Z ≤ cos (rowStep a / 2) := by
    rcases which with h | h
    · rw [h, (colatitude_sub_midpoint a strip).1, cos_neg] at Zu
      simpa only [Z, d, h] using Zu
    · rw [h, (colatitude_sub_midpoint a strip).2] at Zu
      simpa only [Z, d, h] using Zu
  have θ : d = π / (rowSize a row : ℝ) := by unfold d longitudeStep; ring
  obtain ⟨raw_low, raw_up⟩ := rawBaseWidth_bounds positive small row_valid
  have raw_low' : (if isPolarRow a row then 0.432 else 0.952) * spacing a < raw := by
    by_cases h : row = 0 ∨ row = stripCount a <;>
      simpa [raw, θ, isPolarRow, h] using raw_low
  have raw_pos : 0 < raw := lt_trans
    (mul_pos (by cases isPolarRow a row <;> norm_num) (spacing_pos positive)) raw_low'
  have eq : B = raw / Z := by
    change 2 * (sin (colatitude a row) * sin d / Z) = raw / Z
    rw [← mul_div_assoc]
    dsimp only [raw]
    ring
  have upper : raw ≤ spacing a := by
    apply (show raw ≤ localSpacing a row by simpa only [raw, θ] using raw_up).trans
    unfold localSpacing
    split_ifs <;> linarith only [spacing_pos positive]
  change _ < B * _ ∧ B < _
  rw [eq]
  refine ⟨raw_low'.trans_le ?_, ?_⟩
  · exact (div_mul_cancel₀ raw Zp.ne').symm.le.trans
      (mul_le_mul_of_nonneg_left c (div_nonneg raw_pos.le Zp.le))
  · exact (div_le_div_of_nonneg_right upper Zp.le).trans_lt
      (div_lt_div_of_pos_left (spacing_pos positive) (by norm_num) Zl)

end Unfoldings.FewestNets.RevisedLatitudeGrid
