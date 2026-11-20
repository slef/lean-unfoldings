module

public import Unfoldings.Cone.DirectedSlitChart
public import Unfoldings.Cone.SlitFanRestorationBall

/-! A full-turn corner whose two marked banks are joined at the same arclength. -/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace Unfoldings.MarkedSlitFanChart

open MetricGluing

variable {I : Type*} (X : I → Type*) [∀ i, EMetricSpace (X i)]
  (glue : Total X → Total X → Prop) (a : Total X) {ρ ℓ : ℝ}
  (mark : Bool → unitInterval → X a.1)
  (G : MarkedSlitFanChart a.2 (2 * Real.pi) mark (fun _ => ℓ) ρ)

local notation "Patch" => Metric.eball (Sigma.snd a) (ENNReal.ofReal ρ)
local notation "Tag[" x "]" => (Sigma.mk (Sigma.fst a) x : Total X)

include G in
/-- Rejoining the two equal-length rays of a full-turn slit gives a whole planar ball. -/
theorem hasMetricBallChart_of_restored_banks (small : ρ ≤ ℓ)
    (join : ∀ t, point X glue (Tag[mark false t]) = point X glue (Tag[mark true t]))
    (seams : ∀ x y : Patch, glue (Tag[x.val]) (Tag[y.val]) →
      ∃ t : unitInterval, x.val = mark true t ∧ y.val = mark false t ∨
        x.val = mark false t ∧ y.val = mark true t)
    (near_tags : ∀ b (s : ℝ), 0 < s → s ≤ ρ →
      edist (point X glue a) (point X glue b) < ENNReal.ofReal s →
      ∃ x : Patch, Tag[x.val] = b ∧ edist x.val a.2 < ENNReal.ofReal s) :
    HasMetricBallChart ℂ (point X glue a) := by
  let A := G.fan
  let first (r : ℝ≥0) := A.faceMap 0 (A.start 0 r)
  let last (r : ℝ≥0) := A.faceMap (Fin.last G.n) (A.finish (Fin.last G.n) r)
  have heading (r : ℝ≥0) : A.develop (first r) = (r.val : ℂ) := by
    change A.develop (A.faceMap 0 (A.start 0 r)) = _
    rw [A.develop_faceMap, A.place_start, show (0 : Fin (G.n + 1)).castSucc = 0 from rfl,
      A.heading_zero, polarRay_zero, mul_one]
    rfl
  have same_develop (r : ℝ≥0) : A.develop (first r) = A.develop (last r) := by
    change A.develop (A.faceMap 0 (A.start 0 r)) =
      A.develop (A.faceMap (Fin.last G.n) (A.finish (Fin.last G.n) r))
    rw [A.develop_faceMap, A.develop_faceMap]
    exact (A.outer_banks_coincide G.angle_eq r).symm
  have trace (b : Bool) (t : unitInterval) (ht : edist (mark b t) a.2 < ENNReal.ofReal ρ) :
      let r : ℝ≥0 := ⟨t.val * ℓ, mul_nonneg t.property.1 (G.length_pos b).le⟩
      (G.chart ⟨mark b t, ht⟩).val = if b then last r else first r := G.at_bank b t ht
  apply A.hasMetricBallChart_of_restored_slit X glue a G.chart G.angle_eq G.positive G.center
  · intro r x y hx hy
    have radius : ENNReal.ofReal r.val = edist (first r) A.origin := by
      rw [← A.edist_develop_origin, heading, edist_dist, dist_zero_right, Complex.norm_real,
        Real.norm_of_nonneg r.property]
    have less : r.val < ρ := by
      have h := x.property
      change edist x.val A.origin < ENNReal.ofReal ρ at h
      rw [hx, ← radius] at h
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.property).mp h
    have lpos : 0 < ℓ := G.length_pos false
    let t : unitInterval := ⟨r.val / ℓ,
      ⟨div_nonneg r.property lpos.le, (div_le_one lpos).mpr (less.le.trans small)⟩⟩
    have tr : t.val * ℓ = r.val := div_mul_cancel₀ _ lpos.ne'
    have close (b : Bool) : edist (mark b t) a.2 < ENNReal.ofReal ρ := by
      rw [G.radial b t]
      change ENNReal.ofReal (t.val * ℓ) < ENNReal.ofReal ρ
      rw [tr]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.property).mpr less
    have parameters (flag : Bool) :
        (⟨t.val * ℓ, mul_nonneg t.property.1 (G.length_pos flag).le⟩ : ℝ≥0) = r :=
      NNReal.eq tr
    have at_x : G.chart ⟨mark false t, close false⟩ = x := by
      apply Subtype.ext
      exact (trace false t (close false)).trans ((congrArg first (parameters false)).trans hx.symm)
    have at_y : G.chart ⟨mark true t, close true⟩ = y := by
      apply Subtype.ext
      exact (trace true t (close true)).trans ((congrArg last (parameters true)).trans hy.symm)
    rw [← at_x, ← at_y, G.chart.symm_apply_apply, G.chart.symm_apply_apply]
    exact join t
  · intro x y h
    obtain ⟨t, pair⟩ := seams x y h
    have equal {u v : Patch} (hu : u.val = mark false t) (hv : v.val = mark true t) :
        A.develop (G.chart u).val = A.develop (G.chart v).val := by
      let r : ℝ≥0 := ⟨t.val * ℓ, mul_nonneg t.property.1 (G.length_pos false).le⟩
      have u_near : edist (mark false t) a.2 < ENNReal.ofReal ρ := hu ▸ u.property
      have v_near : edist (mark true t) a.2 < ENNReal.ofReal ρ := hv ▸ v.property
      have u_eq : u = ⟨mark false t, u_near⟩ := Subtype.ext hu
      have v_eq : v = ⟨mark true t, v_near⟩ := Subtype.ext hv
      rw [u_eq, v_eq]
      exact (congrArg A.develop (trace false t u_near)).trans
        ((same_develop r).trans (congrArg A.develop (trace true t v_near)).symm)
    exact pair.elim (fun h => (equal h.2 h.1).symm) (fun h => equal h.1 h.2)
  · exact near_tags

end Unfoldings.MarkedSlitFanChart
