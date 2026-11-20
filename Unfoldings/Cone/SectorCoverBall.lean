module

public import Unfoldings.Metric.BallFromLocalSteps
public import Unfoldings.Metric.ConvexCover
public import Unfoldings.Metric.Polygonal
public import Unfoldings.Metric.BallChart

/-! Finite compatible sector charts, including several copies of one original piece. -/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace Unfoldings.MetricGluing

variable {I J : Type*} (X : I → Type*) [∀ i, EMetricSpace (X i)]
  (center : J → Total X) (regions : J → Set ℂ)
  (origin : ∀ j, PolygonalPoint (regions j)) (ρ : ℝ)

/-- A whole intrinsic ball in each original piece, centered at a specified copy. -/
structure SectorCoverChart where
  positive : 0 < ρ
  chart (j : J) :
    Metric.eball (center j).2 (ENNReal.ofReal ρ) ≃ᵢ Metric.eball (origin j) (ENNReal.ofReal ρ)
  centered (j : J) :
    (chart j ⟨(center j).2, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val =
      origin j
  radial (j : J) (z : PolygonalPoint (regions j)) :
    edist z (origin j) = edist z.val (0 : ℂ)
  separated (j k : J) (distinct : j ≠ k) (tag : (center j).1 = (center k).1)
    (x : Metric.eball (center j).2 (ENNReal.ofReal ρ))
    (y : Metric.eball (center k).2 (ENNReal.ofReal ρ)) :
    ENNReal.ofReal (2 * ρ) ≤ edist (tag ▸ x.val) y.val

namespace SectorCoverChart

variable {X center regions origin ρ} (A : SectorCoverChart X center regions origin ρ)

local notation "Ball[" j "]" => Metric.eball (Sigma.snd (center j)) (ENNReal.ofReal ρ)
local notation "Model[" j "]" => Metric.eball (origin j) (ENNReal.ofReal ρ)

def patchTag (_A : SectorCoverChart X center regions origin ρ) (j : J) (x : Ball[j]) : Total X := ⟨(center j).1, x.val⟩

def modelTag (j : J) (z : Model[j]) : Total X := A.patchTag j ((A.chart j).symm z)

theorem radial_chart (j : J) (x : Ball[j]) :
    edist (A.chart j x).val.val (0 : ℂ) = edist x.val (center j).2 := by
  have e := (A.chart j).isometry.edist_eq x
    ⟨(center j).2, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr A.positive)⟩
  change edist (A.chart j x).val
      (A.chart j ⟨(center j).2, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr A.positive)⟩).val =
    edist x.val (center j).2 at e
  rw [A.centered] at e
  exact (A.radial j _).symm.trans e

private theorem tagged_value {p q : Total X} (h : p = q) :
    ((congrArg Sigma.fst h) ▸ p.2) = q.2 := by
  subst q
  rfl

private theorem tagged_injective : Function.Injective (fun p : Σ j, Ball[j] => A.patchTag p.1 p.2) := by
  rintro ⟨j, x⟩ ⟨k, y⟩ equal
  have tag := congrArg (fun p : Total X => p.1) equal
  have value : (tag ▸ x.val) = y.val := tagged_value equal
  by_cases same : j = k
  · subst k
    exact congrArg (Sigma.mk j) (Subtype.ext (eq_of_heq (Sigma.mk.inj equal).2))
  · have positive := ENNReal.ofReal_pos.mpr (mul_pos two_pos A.positive)
    have impossible := (congrArg (edist · y.val) value).trans (edist_self _)
    exact (not_lt_of_ge (A.separated j k same tag x y) (impossible.trans_lt positive)).elim

def coordinates (x : Total X) : ℂ := by
  classical
  exact if h : ∃ p : Σ j, Ball[j], A.patchTag p.1 p.2 = x then
    (A.chart h.choose.1 h.choose.2).val.val else 0

@[simp] theorem coordinates_tag (j : J) (x : Ball[j]) :
    A.coordinates (A.patchTag j x) = (A.chart j x).val.val := by
  classical
  unfold coordinates
  let h : ∃ p : Σ j, Ball[j], A.patchTag p.1 p.2 = A.patchTag j x := ⟨⟨j,x⟩, rfl⟩
  rw [dite_eq_left h]
  have same : h.choose = (⟨j, x⟩ : Σ j, Ball[j]) := A.tagged_injective h.choose_spec
  exact congrArg (fun p : Σ j, Ball[j] => (A.chart p.1 p.2).val.val) same

@[simp] theorem coordinates_modelTag (j : J) (z : Model[j]) :
    A.coordinates (A.modelTag j z) = z.val.val := by
  rw [modelTag, A.coordinates_tag, (A.chart j).apply_symm_apply]

variable {glue : Total X → Total X → Prop}

private theorem coordinate_step
    (compatible : ∀ (j k : J) (x : Ball[j]) (y : Ball[k]),
      glue (A.patchTag j x) (A.patchTag k y) → (A.chart j x).val.val = (A.chart k y).val.val)
    (j k : J) (x : Ball[j]) (y : Ball[k]) :
    edist (A.chart j x).val.val (A.chart k y).val.val ≤
      stepCost X glue (A.patchTag j x) (A.patchTag k y) := by
  classical
  unfold stepCost
  split
  · rename_i joined
    have eq := joined.elim (compatible j k x y) (fun h => (compatible k j y x h).symm)
    rw [eq, edist_self]
  · by_cases same : j = k
    · subst k
      rw [patchTag, patchTag, faceCost, dite_eq_left rfl]
      exact (PolygonalPoint.ambient_edist_le_distance _ _).trans_eq
        ((A.chart j).isometry.edist_eq x y)
    · by_cases tags : (center j).1 = (center k).1
      · have x_radius := (A.radial_chart j x).trans_lt x.property
        have y_radius := (A.radial_chart k y).trans_lt y.property
        have bound := (edist_triangle (A.chart j x).val.val 0 (A.chart k y).val.val).trans
          (add_le_add x_radius.le ((edist_comm _ _).trans_lt y_radius).le)
        have scale : ENNReal.ofReal ρ + ENNReal.ofReal ρ = ENNReal.ofReal (2 * ρ) := by
          rw [← ENNReal.ofReal_add A.positive.le A.positive.le, two_mul]
        rw [patchTag, patchTag, faceCost, dite_eq_left tags]
        exact (bound.trans_eq scale).trans (A.separated j k same tags x y)
      · simp [patchTag, faceCost, tags]

theorem modelTag_origin (j : J) :
    A.modelTag j ⟨origin j, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr A.positive)⟩ =
      center j := by
  let x : Ball[j] := ⟨(center j).2, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr A.positive)⟩
  have center_image : A.chart j x =
      ⟨origin j, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr A.positive)⟩ :=
    Subtype.ext (A.centered j)
  rw [modelTag, (A.chart j).symm_apply_eq.mpr center_image.symm]
  exact Sigma.eta (center j)

variable {L : Type*} [Finite L] (cell : L → Set ℂ) (owner : L → J)
  (inside : ∀ l, cell l ⊆ regions (owner l))

/-- Restrict a geometric point in a convex subcell to its owner's intrinsic model ball. -/
def cellPoint (l : L) {z : ℂ} (hz : z ∈ cell l) (near : edist z 0 < ENNReal.ofReal ρ) :
    Model[owner l] :=
  ⟨⟨z, inside l hz⟩, (A.radial (owner l) _).trans_lt near⟩

include owner inside in
/-- Consistently placed convex subcells give a whole planar ball at the common center.
Distinct center copies may have the same tag in the original gluing. -/
theorem hasMetricBallChart (j₀ : J) (closed : ∀ l, IsClosed (cell l))
    (convex : ∀ l, Convex ℝ (cell l))
    (covers : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∃ l, z ∈ cell l)
    (shared : ∀ (j k : J) (z : Model[j]) (w : Model[k]), z.val.val = w.val.val →
      point X glue (A.modelTag j z) = point X glue (A.modelTag k w))
    (compatible : ∀ (j k : J) (x : Ball[j]) (y : Ball[k]),
      glue (A.patchTag j x) (A.patchTag k y) → (A.chart j x).val.val = (A.chart k y).val.val)
    (near_tags : ∀ b (r : ℝ), 0 < r → r ≤ ρ →
      edist (point X glue (center j₀)) (point X glue b) < ENNReal.ofReal r →
      ∃ (j : J) (x : Ball[j]), A.patchTag j x = b ∧ edist x.val (center j).2 < ENNReal.ofReal r) :
    HasMetricBallChart ℂ (point X glue (center j₀)) := by
  classical
  let r := ρ / 4
  have rpos : 0 < r := div_pos A.positive (by norm_num)
  have rsmall : r ≤ ρ := by dsimp [r]; linarith [A.positive]
  have four_r : 4 * r = ρ := by dsimp [r]; ring
  let Disk := Metric.ball (0 : ℂ) r
  have edist_near (z : Disk) : edist z.val (0 : ℂ) < ENNReal.ofReal r := by
    rw [edist_dist]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg |>.mpr z.property
  have covers_small (z : Disk) : ∃ l, z.val ∈ cell l :=
    covers z.val (Metric.ball_subset_ball rsmall z.property)
  choose index member using covers_small
  let atCell (z : Disk) (l : L) (hz : z.val ∈ cell l) : Model[owner l] :=
    A.cellPoint cell owner inside l hz
      ((edist_near z).trans_le (ENNReal.ofReal_le_ofReal rsmall))
  let fill (z : Disk) := point X glue (A.modelTag (owner (index z)) (atCell z (index z) (member z)))
  have fill_at (z : Disk) (j : J) (w : Model[j]) (equal : w.val.val = z.val) :
      fill z = point X glue (A.modelTag j w) := shared _ _ _ _ equal.symm
  let patch (l : L) : Set Disk := Subtype.val ⁻¹' cell l
  have patch_closed (l : L) : IsClosed (patch l) := (closed l).preimage continuous_subtype_val
  have patch_cover : ⋃ l, patch l = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    exact Set.mem_iUnion.mpr ⟨index z, member z⟩
  have patch_lipschitz (l : L) : LipschitzOnWith 1 fill (patch l) := by
    intro z hz w hw
    let x := atCell z l hz
    let y := atCell w l hw
    rw [fill_at z (owner l) x rfl, fill_at w (owner l) y rfl]
    have eq : edist x.val y.val = edist z.val w.val :=
      PolygonalPoint.edist_eq_of_segment (x := x.val) (y := y.val)
        (((convex l).segment_subset hz hw).trans (inside l))
    rw [ENNReal.coe_one, one_mul, Subtype.edist_eq, ← eq]
    exact (edist_of_le X glue (center (owner l)).1 _ _).trans_eq
      ((A.chart (owner l)).symm.isometry.edist_eq x y)
  have nonexpanding := convex_subtype_emetric_lipschitzWith_of_finite_closed_cover
    (Metric.ball (0 : ℂ) r) (convex_ball _ _) patch patch_closed patch_cover fill 1 patch_lipschitz
  have fills_center : fill ⟨0, Metric.mem_ball_self rpos⟩ = point X glue (center j₀) := by
    have at_zero : (origin j₀).val = 0 :=
      edist_eq_zero.mp ((A.radial j₀ (origin j₀)).symm.trans (edist_self _))
    rw [fill_at _ j₀ ⟨origin j₀, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr A.positive)⟩
      at_zero, A.modelTag_origin]
  have reps (z : Disk) : ∃ b, point X glue b = fill z ∧ A.coordinates b = z.val :=
    ⟨A.modelTag (owner (index z)) (atCell z (index z) (member z)), rfl,
      A.coordinates_modelTag _ _⟩
  have covers_ball (x : Realization X glue)
      (hx : x ∈ Metric.eball (point X glue (center j₀)) (ENNReal.ofReal r)) : ∃ z, fill z = x := by
    obtain ⟨b, rfl⟩ := point_surjective X glue x
    obtain ⟨j, u, rfl, hu⟩ := near_tags b r rpos rsmall ((edist_comm _ _).trans_lt hx)
    let z := A.chart j u
    have ambient : z.val.val ∈ Metric.ball (0 : ℂ) r := by
      have estimate := (A.radial_chart j u).trans_lt hu
      rw [edist_dist] at estimate
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp estimate
    refine ⟨⟨z.val.val, ambient⟩, ?_⟩
    rw [fill_at _ j z rfl]
    dsimp [z, modelTag]
    rw [(A.chart j).symm_apply_apply]
  have steps (b c : Total X)
      (hb : edist (point X glue (center j₀)) (point X glue b) < ENNReal.ofReal (4 * r))
      (hc : edist (point X glue (center j₀)) (point X glue c) < ENNReal.ofReal (4 * r)) :
      edist (A.coordinates b) (A.coordinates c) ≤ stepCost X glue b c := by
    rw [four_r] at hb hc
    obtain ⟨j, z, rfl, _⟩ := near_tags b ρ A.positive le_rfl hb
    obtain ⟨k, w, rfl, _⟩ := near_tags c ρ A.positive le_rfl hc
    rw [A.coordinates_tag, A.coordinates_tag]
    exact A.coordinate_step compatible j k z w
  obtain ⟨chart, _⟩ := ball_isometry_of_local_steps X glue (center j₀) 0 rpos
    A.coordinates steps fill nonexpanding fills_center reps covers_ball
  exact ⟨r, rpos, 0, ⟨chart.symm⟩⟩

end SectorCoverChart

end Unfoldings.MetricGluing
