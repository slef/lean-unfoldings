module

public import Unfoldings.Cone.AngularClosure
public import Unfoldings.Cone.AngularChord
public import Unfoldings.Metric.BallFromLocalSteps
public import Unfoldings.Metric.BallChart

/-! Restoring the two banks of a full-turn slit in an ambient metric gluing. -/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace Unfoldings.AngularFan

open MetricGluing

variable {n : ℕ} (A : AngularFan n)

/-- Development preserves the radial distance even when it identifies the two banks. -/
theorem edist_develop_origin (x : A.Surface) : edist (A.develop x) 0 = edist x A.origin := by
  obtain ⟨⟨i, p⟩, rfl⟩ := point_surjective A.Cell A.glue x
  change edist (A.develop (A.faceMap i p)) 0 = edist (A.faceMap i p) A.origin
  rw [A.develop_faceMap, edist_comm (A.faceMap i p), A.edist_origin_faceMap, edist_comm 0]
  have zero : A.place i (A.start i 0) = 0 := by rw [A.place_start]; simp
  have start_zero : (A.start i 0).val = 0 := by simp [start]
  simpa only [zero, Subtype.edist_eq, start_zero] using A.place_isometry i p (A.start i 0)

variable {I : Type*} (X : I → Type*) [∀ i, PseudoEMetricSpace (X i)]
  (glue : Total X → Total X → Prop) (a : Total X) {ρ : ℝ}
  (chart : Metric.eball a.2 (ENNReal.ofReal ρ) ≃ᵢ
    Metric.eball A.origin (ENNReal.ofReal ρ))

local notation "Patch" => Metric.eball (Sigma.snd a) (ENNReal.ofReal ρ)
local notation "Model" => Metric.eball (AngularFan.origin A) (ENNReal.ofReal ρ)
local notation "Tag" => fun x : Patch => (Sigma.mk (Sigma.fst a) (Subtype.val x) : Total X)
local notation "xy" => fun x : Patch => AngularFan.develop A (Subtype.val (chart x))

/-- The actual ball is planar if all near representatives come from one full-turn
slit chart, its outer banks are rejoined, and the seams respect its development. -/
theorem hasMetricBallChart_of_restored_slit (full : A.totalAngle = 2 * Real.pi) (positive : 0 < ρ)
    (apex : (chart ⟨a.2, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val = A.origin)
    (outer : ∀ (r : ℝ≥0) (x y : Model),
      x.val = A.faceMap 0 (A.start 0 r) →
      y.val = A.faceMap (Fin.last n) (A.finish (Fin.last n) r) →
      point X glue (Tag (chart.symm x)) = point X glue (Tag (chart.symm y)))
    (compatible : ∀ x y : Patch, glue (Tag x) (Tag y) → xy x = xy y)
    (near_tags : ∀ b (s : ℝ), 0 < s → s ≤ ρ →
      edist (point X glue a) (point X glue b) < ENNReal.ofReal s →
      ∃ x : Patch, Tag x = b ∧ edist x.val a.2 < ENNReal.ofReal s) :
    HasMetricBallChart ℂ (point X glue a) := by
  classical
  let r := ρ / 4
  have rpos : 0 < r := div_pos positive (by norm_num)
  have rle : r ≤ ρ := by dsimp [r]; linarith
  have four_r : 4 * r = ρ := by dsimp [r]; ring
  let a₀ : Patch := ⟨a.2, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩
  have tag_inj : Function.Injective Tag := fun x y h =>
    Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  let coordinates (b : Total X) : ℂ := if h : ∃ x : Patch, Tag x = b then xy h.choose else 0
  have coordinates_tag (x : Patch) : coordinates (Tag x) = xy x := by
    have exists_tag : ∃ y : Patch, Tag y = Tag x := ⟨x, rfl⟩
    dsimp only [coordinates]
    rw [dite_eq_left exists_tag, tag_inj exists_tag.choose_spec]
  let Disk := Metric.ball (0 : ℂ) r
  have radial (x : Patch) : edist (xy x) 0 = edist x.val a.2 := by
    rw [A.edist_develop_origin]
    have h := chart.isometry.edist_eq x a₀
    change edist (chart x).val (chart a₀).val = edist x.val a.2 at h
    have at_apex : (chart a₀).val = A.origin := apex
    rw [at_apex] at h
    exact h
  have near (z : Disk) : edist z.val 0 < ENNReal.ofReal r := by
    rw [edist_dist]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg |>.mpr z.property
  have preimage (z : Disk) : ∃ x : Model, A.develop x.val = z.val := by
    obtain ⟨x, hx⟩ := A.develop_surjective_of_full full z.val
    refine ⟨⟨x, ?_⟩, hx⟩
    rw [Metric.mem_eball, ← A.edist_develop_origin, hx]
    exact (near z).trans_le (ENNReal.ofReal_le_ofReal rle)
  choose lift aligned using preimage
  let fill (z : Disk) := point X glue (Tag (chart.symm (lift z)))
  have shared (x y : Model) (eq : A.develop x.val = A.develop y.val) :
      point X glue (Tag (chart.symm x)) = point X glue (Tag (chart.symm y)) := by
    rcases A.develop_fiber_cases full x.val y.val eq with same | ⟨s, first | last⟩
    · rw [show x = y from Subtype.ext same]
    · exact outer s x y first.1 first.2
    · exact (outer s y x last.2 last.1).symm
  have fill_at (z : Disk) (w : Model) (eq : A.develop w.val = z.val) :
      fill z = point X glue (Tag (chart.symm w)) :=
    shared (lift z) w ((aligned z).trans eq.symm)
  let patch (i : Fin (n + 1)) : Set Disk := Subtype.val ⁻¹' A.faceImage i
  have patch_closed (i : Fin (n + 1)) : IsClosed (patch i) :=
    (A.isClosed_faceImage i).preimage continuous_subtype_val
  have patch_cover : ⋃ i, patch i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    have hz : z.val ∈ ⋃ i, A.faceImage i := by rw [A.faceImage_cover_of_full full]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have patch_bound (i : Fin (n + 1)) : LipschitzOnWith 1 fill (patch i) := by
    intro z hz w hw
    obtain ⟨p, hp, first⟩ := hz
    obtain ⟨q, hq, last⟩ := hw
    let u : A.Cell i := ⟨p, hp⟩
    let v : A.Cell i := ⟨q, hq⟩
    change A.place i u = z.val at first
    change A.place i v = w.val at last
    have to_model (z : Disk) (u : A.Cell i) (eq : A.place i u = z.val) :
        edist (A.faceMap i u) A.origin < ENNReal.ofReal ρ := by
      rw [← A.edist_develop_origin, A.develop_faceMap, eq]
      exact (near z).trans_le (ENNReal.ofReal_le_ofReal rle)
    let x : Model := ⟨A.faceMap i u, to_model z u first⟩
    let y : Model := ⟨A.faceMap i v, to_model w v last⟩
    rw [fill_at z x ((A.develop_faceMap i u).trans first),
      fill_at w y ((A.develop_faceMap i v).trans last), ENNReal.coe_one, one_mul]
    calc
      _ ≤ edist (chart.symm x).val (chart.symm y).val := edist_of_le X glue a.1 _ _
      _ = edist x.val y.val := chart.symm.isometry.edist_eq x y
      _ = edist z w := by
        change edist (A.faceMap i u) (A.faceMap i v) = edist z.val w.val
        rw [A.faceMap_isometry i, ← (A.place_isometry i).edist_eq, first, last]
  have nonexpanding := convex_subtype_emetric_lipschitzWith_of_finite_closed_cover
    (Metric.ball (0 : ℂ) r) (convex_ball _ _) patch patch_closed patch_cover fill 1 patch_bound
  have center : fill ⟨0, Metric.mem_ball_self rpos⟩ = point X glue a := by
    rw [fill_at _ (chart a₀) (by rw [apex, A.develop_origin]), chart.symm_apply_apply]
  have reps (z : Disk) : ∃ b, point X glue b = fill z ∧ coordinates b = z.val := by
    refine ⟨Tag (chart.symm (lift z)), rfl, ?_⟩
    rw [coordinates_tag]
    change A.develop (chart (chart.symm (lift z))).val = z.val
    rw [chart.apply_symm_apply, aligned]
  have covers (z : Realization X glue)
      (hz : z ∈ Metric.eball (point X glue a) (ENNReal.ofReal r)) : ∃ w, fill w = z := by
    obtain ⟨b, rfl⟩ := point_surjective X glue z
    obtain ⟨x, rfl, hx⟩ := near_tags b r rpos rle ((edist_comm _ _).trans_lt hz)
    have on_disk : xy x ∈ Disk := by
      have bound := (radial x).trans_lt hx
      rw [edist_dist] at bound
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp bound
    exact ⟨⟨xy x, on_disk⟩, (fill_at _ (chart x) rfl).trans
      (congrArg (fun u => point X glue (Tag u)) (chart.symm_apply_apply x))⟩
  have steps (b c : Total X)
      (hb : edist (point X glue a) (point X glue b) < ENNReal.ofReal (4 * r))
      (hc : edist (point X glue a) (point X glue c) < ENNReal.ofReal (4 * r)) :
      edist (coordinates b) (coordinates c) ≤ stepCost X glue b c := by
    rw [four_r] at hb hc
    obtain ⟨x, rfl, _⟩ := near_tags b ρ positive le_rfl hb
    obtain ⟨y, rfl, _⟩ := near_tags c ρ positive le_rfl hc
    rw [coordinates_tag, coordinates_tag, stepCost]
    split
    · rename_i joint
      rw [joint.elim (compatible x y) (fun h => (compatible y x h).symm), edist_self]
    · rw [faceCost, dite_eq_left rfl]
      have bound := A.develop_lipschitz.edist_le_mul (chart x).val (chart y).val
      simp only [ENNReal.coe_one, one_mul] at bound
      exact bound.trans_eq (chart.isometry.edist_eq x y)
  obtain ⟨result, _⟩ := ball_isometry_of_local_steps X glue a 0 rpos coordinates steps fill
    nonexpanding center reps covers
  exact ⟨r, rpos, 0, ⟨result.symm⟩⟩

end Unfoldings.AngularFan
