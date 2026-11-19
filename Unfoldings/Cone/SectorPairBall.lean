module

public import Unfoldings.Cone.ComplementarySectorRadial
public import Unfoldings.Metric.BallFromLocalSteps
public import Unfoldings.Metric.BankPairNeighborhood

/-! Local comparison with the full complementary-sector metric. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing

variable {I : Type*} (X : I → Type*) [∀ i, EMetricSpace (X i)]
  (glue : Total X → Total X → Prop) (a : Bool → Total X)
  {θ : ℝ} (pos : 0 < θ) (small : θ < 2 * Real.pi) {R : ℝ}

local notation "Y" => (fun b => PolygonalPoint (complementarySectorRegion θ b))
local notation "origin" => complementarySectorOrigin pos small
local notation "assembly" => complementarySectorPlaneIsometryEquiv θ pos small
local notation "coincident" => polygonalCoincident (complementarySectorRegion θ)
local notation "ctr" => point X glue (a false)
local notation "ρ" => ENNReal.ofReal R

/-- Two original piece balls carry actual complementary sector charts. -/
structure SectorPairChart (radius : ℝ) where
  positive : 0 < radius
  distinct : (a false).1 ≠ (a true).1
  chart (b : Bool) :
    Metric.eball (a b).2 (ENNReal.ofReal radius) ≃ᵢ
      Metric.eball (origin b) (ENNReal.ofReal radius)
  centered (b : Bool) :
    (chart b ⟨(a b).2, (edist_self _).trans_lt (ENNReal.ofReal_pos.mpr positive)⟩).val =
      origin b

namespace SectorPairChart

variable {X glue a pos small} (C : SectorPairChart X a pos small R)

def pairTag {I : Type*} {X : I → Type*} [∀ i, EMetricSpace (X i)] (a : Bool → Total X)
    {r : ℝ≥0∞} (b : Bool) (x : Metric.eball (a b).2 r) : Total X :=
  ⟨(a b).1, x.val⟩

local notation "tag" => pairTag a

def inverseTag (b : Bool) (x : Metric.eball (origin b) ρ) : Total X :=
  tag b ((C.chart b).symm x)

include C in
private theorem index_injective : Function.Injective (fun b => (a b).1) := by
  intro b c h
  cases b <;> cases c
  · rfl
  · exact (C.distinct h).elim
  · exact (C.distinct h.symm).elim
  · rfl

include C in
private theorem tag_eq {b c : Bool} (x : Metric.eball (a b).2 ρ)
    (y : Metric.eball (a c).2 ρ) (h : tag b x = tag c y) :
    (⟨b, x⟩ : Σ b, Metric.eball (a b).2 ρ) = ⟨c, y⟩ := by
  have tags := congrArg (fun z : Total X => z.1) h
  have same : b = c := C.index_injective tags
  subst c
  have aligned := (Sigma.mk.inj_iff.mp h).2
  exact congrArg (Sigma.mk b) (Subtype.ext (eq_of_heq aligned))

/-- A default value is used only away from the actual piece balls. -/
def coordinates (z : Total X) : ℂ := by
  classical
  exact if h : ∃ p : Σ b, Metric.eball (a b).2 ρ, tag p.1 p.2 = z then
    (C.chart h.choose.1 h.choose.2).val.val else 0

@[simp] theorem coordinates_tag (b : Bool) (x : Metric.eball (a b).2 ρ) :
    C.coordinates (tag b x) = (C.chart b x).val.val := by
  classical
  unfold coordinates
  let h : ∃ p : Σ b, Metric.eball (a b).2 ρ, tag p.1 p.2 = tag b x := ⟨⟨b, x⟩, rfl⟩
  rw [dite_eq_left h]
  exact congrArg (fun p : Σ b, Metric.eball (a b).2 ρ => (C.chart p.1 p.2).val.val)
    (C.tag_eq h.choose.2 x h.choose_spec)

@[simp] theorem coordinates_inverseTag (b : Bool) (x : Metric.eball (origin b) ρ) :
    C.coordinates (C.inverseTag b x) = x.val.val := by
  rw [inverseTag, C.coordinates_tag, (C.chart b).apply_symm_apply]

private theorem chart_radial (b : Bool) (x : Metric.eball (a b).2 ρ) :
    edist (C.chart b x).val.val (0 : ℂ) = edist x.val (a b).2 := by
  have equal := (C.chart b).isometry.edist_eq x
    ⟨(a b).2, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr C.positive)⟩
  change edist (C.chart b x).val
    (C.chart b ⟨(a b).2, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr C.positive)⟩).val =
      edist x.val (a b).2 at equal
  rw [C.centered, edist_complementarySectorOrigin] at equal
  exact equal

private theorem inverseTag_center (b : Bool) :
    C.inverseTag b ⟨origin b, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr C.positive)⟩ =
      a b := by
  let x : Metric.eball (a b).2 ρ :=
    ⟨(a b).2, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr C.positive)⟩
  let y : Metric.eball (origin b) ρ :=
    ⟨origin b, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr C.positive)⟩
  have image : C.chart b x = y := Subtype.ext (C.centered b)
  change pairTag a b ((C.chart b).symm y) = a b
  rw [(C.chart b).symm_apply_eq.mpr image.symm]
  exact Sigma.eta (a b)

variable
  (compatible : ∀ (b c : Bool)
    (x : Metric.eball (a b).2 (ENNReal.ofReal R))
    (y : Metric.eball (a c).2 (ENNReal.ofReal R)),
    glue (pairTag a b x) (pairTag a c y) → (C.chart b x).val.val = (C.chart c y).val.val)
  (shared : ∀ (b c : Bool)
    (x : Metric.eball (complementarySectorOrigin pos small b) (ENNReal.ofReal R))
    (y : Metric.eball (complementarySectorOrigin pos small c) (ENNReal.ofReal R)),
    x.val.val = y.val.val → point X glue (C.inverseTag b x) = point X glue (C.inverseTag c y))
  (near_tags : ∀ (r : ℝ), r ≤ R → ∀ z : Total X,
    edist (point X glue z) (point X glue (a false)) < ENNReal.ofReal r →
      ∃ (b : Bool) (x : Metric.eball (a b).2 (ENNReal.ofReal R)),
      pairTag a b x = z ∧ edist x.val (a b).2 < ENNReal.ofReal r)

include compatible near_tags in
private theorem coordinate_step (z w : Total X) (hz : edist ctr (point X glue z) < ρ)
    (hw : edist ctr (point X glue w) < ρ) :
    edist (C.coordinates z) (C.coordinates w) ≤ stepCost X glue z w := by
  classical
  obtain ⟨b, x, rfl, _⟩ := near_tags R le_rfl z ((edist_comm _ _).trans_lt hz)
  obtain ⟨c, y, rfl, _⟩ := near_tags R le_rfl w ((edist_comm _ _).trans_lt hw)
  rw [C.coordinates_tag, C.coordinates_tag]
  unfold stepCost
  split
  · rename_i joined
    rcases joined with first | last
    · rw [compatible b c x y first, edist_self]
    · rw [compatible c b y x last, edist_self]
  · by_cases same : b = c
    · subst c
      rw [pairTag, pairTag, faceCost_same_tag]
      exact (PolygonalPoint.ambient_edist_le_distance (C.chart b x).val (C.chart b y).val).trans_eq
        ((C.chart b).isometry.edist_eq x y)
    · have diff : (a b).1 ≠ (a c).1 := C.index_injective.ne same
      simp [pairTag, faceCost, diff]

include shared in
private theorem centers_glued (b : Bool) : point X glue (a b) = ctr := by
  let o (c : Bool) : Metric.eball (origin c) ρ :=
    ⟨origin c, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr C.positive)⟩
  exact (congrArg (point X glue) (C.inverseTag_center b)).symm.trans
    ((shared b false (o b) (o false) rfl).trans
      (congrArg (point X glue) (C.inverseTag_center false)))

include pos small in
private theorem model_edist (z w : Total Y) :
    edist (point Y coincident z) (point Y coincident w) = edist z.2.val w.2.val :=
  ((assembly).isometry.edist_eq _ _).symm

private def restore (z : Total Y) : Realization X glue := by
  classical
  exact if near : edist z.2 (origin z.1) < ρ then
    point X glue (C.inverseTag z.1 ⟨z.2, near⟩) else ctr

private theorem restore_of_near (b : Bool) (x : Metric.eball (origin b) ρ) :
    C.restore (glue := glue) ⟨b, x.val⟩ = point X glue (C.inverseTag b x) := by
  classical
  unfold restore
  exact dite_eq_left x.property

include shared in
private theorem restore_radial (z : Total Y) (near : edist z.2.val (0 : ℂ) < ρ) :
    edist (C.restore (glue := glue) z) ctr ≤ edist z.2.val (0 : ℂ) := by
  obtain ⟨b, x⟩ := z
  let y : Metric.eball (origin b) ρ := ⟨x, (edist_complementarySectorOrigin pos small b x).trans_lt
    near⟩
  rw [show (⟨b, x⟩ : Total Y) = ⟨b, y.val⟩ from rfl, C.restore_of_near b y,
    ← C.centers_glued shared b]
  exact (edist_of_le X glue _ _ _).trans_eq
    (C.chart_radial b ((C.chart b).symm y)).symm |>.trans_eq
      (by rw [(C.chart b).apply_symm_apply y])

include shared in
private theorem restore_step (z w : Total Y)
    (hz : edist z.2.val (0 : ℂ) < ρ) (hw : edist w.2.val (0 : ℂ) < ρ) :
    edist (C.restore (glue := glue) z) (C.restore (glue := glue) w) ≤
      stepCost Y coincident z w := by
  classical
  obtain ⟨b, x⟩ := z
  obtain ⟨c, y⟩ := w
  let x' : Metric.eball (origin b) ρ :=
    ⟨x, (edist_complementarySectorOrigin pos small b x).trans_lt hz⟩
  let y' : Metric.eball (origin c) ρ :=
    ⟨y, (edist_complementarySectorOrigin pos small c y).trans_lt hw⟩
  rw [show (⟨b, x⟩ : Total Y) = ⟨b, x'.val⟩ from rfl, C.restore_of_near b x',
    show (⟨c, y⟩ : Total Y) = ⟨c, y'.val⟩ from rfl, C.restore_of_near c y']
  unfold stepCost
  split
  · rename_i coincides
    have equal : x'.val.val = y'.val.val := coincides.elim id Eq.symm
    rw [shared b c x' y' equal, edist_self]
  · by_cases same : b = c
    · subst c
      rw [faceCost_same_tag]
      exact (edist_of_le X glue _ _ _).trans_eq
        ((C.chart b).symm.isometry.edist_eq x' y')
    · simp [faceCost, same]

private theorem exists_model_tag (z : ℂ) : ∃ p : Total Y, p.2.val = z := by
  have cover := closedAngularSector_union_complementary θ
  have member : z ∈ closedAngularSector θ ∪ complementarySector θ :=
    cover.symm ▸ Set.mem_univ z
  rcases member with first | second
  · exact ⟨⟨false, ⟨z, first⟩⟩, rfl⟩
  · exact ⟨⟨true, ⟨z, second⟩⟩, rfl⟩

private def modelTag (z : ℂ) : Total Y := (exists_model_tag (θ := θ) z).choose

private theorem modelTag_val (z : ℂ) : (modelTag (θ := θ) z).2.val = z :=
  (exists_model_tag (θ := θ) z).choose_spec

private theorem ball_near {r : ℝ} (z : Metric.ball (0 : ℂ) r) :
    edist z.val (0 : ℂ) < ENNReal.ofReal r := by
  rw [edist_dist]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr z.property

include compatible shared near_tags in
/-- Full original piece coverage and agreement on the two actual common rays give a
whole planar metric ball in the actual glued space. -/
theorem hasMetricBallChart :
    HasMetricBallChart ℂ ctr := by
  let r := R / 4
  have rpos : 0 < r := div_pos C.positive (by norm_num)
  have scale : 4 * r = R := by dsimp [r]; ring
  have small_radius : r ≤ R := by dsimp [r]; linarith [C.positive]
  have radius_le : ENNReal.ofReal r ≤ ρ := ENNReal.ofReal_le_ofReal small_radius
  let fill (z : Metric.ball (0 : ℂ) r) := C.restore (glue := glue) (modelTag (θ := θ) z.val)
  let base : Total Y := ⟨false, origin false⟩
  have model_near (z : Metric.ball (0 : ℂ) r) :
      edist (modelTag (θ := θ) z.val).2.val (0 : ℂ) < ρ := by
    rw [modelTag_val (θ := θ)]
    exact (ball_near z).trans_le radius_le
  have filling_lipschitz : LipschitzWith 1 fill := by
    intro z w
    rw [ENNReal.coe_one, one_mul]
    have steps (x y : Total Y) (hx : edist (point Y coincident base) (point Y coincident x) < ρ)
        (hy : edist (point Y coincident base) (point Y coincident y) < ρ) :=
      C.restore_step shared x y (by
        rw [model_edist (pos := pos) (small := small), edist_comm] at hx
        exact hx) (by
        rw [model_edist (pos := pos) (small := small), edist_comm] at hy
        exact hy)
    have bound_z := C.restore_radial shared (modelTag (θ := θ) z.val) (model_near z)
    have bound_w := C.restore_radial shared (modelTag (θ := θ) w.val) (model_near w)
    have radial_z : edist (fill z) ctr ≤ edist z.val (0 : ℂ) :=
      bound_z.trans_eq (congrArg (edist · (0 : ℂ)) (modelTag_val (θ := θ) z.val))
    have radial_w : edist (fill w) ctr ≤ edist w.val (0 : ℂ) :=
      bound_w.trans_eq (congrArg (edist · (0 : ℂ)) (modelTag_val (θ := θ) w.val))
    have budget : edist (point Y coincident base) (point Y coincident (modelTag (θ := θ) z.val)) +
        edist (fill z) (fill w) < ρ := by
      rw [model_edist (pos := pos) (small := small), modelTag_val (θ := θ)]
      change edist (0 : ℂ) z.val + edist (fill z) (fill w) < ρ
      apply lt_of_le_of_lt (add_le_add le_rfl ((edist_triangle (fill z) ctr (fill w)).trans
        (add_le_add radial_z ((edist_comm ctr (fill w)).trans_le radial_w))))
      rw [edist_comm (0 : ℂ), edist_dist, edist_dist,
        ← ENNReal.ofReal_add dist_nonneg dist_nonneg,
        ← ENNReal.ofReal_add dist_nonneg (add_nonneg dist_nonneg dist_nonneg), ← scale]
      apply ENNReal.ofReal_lt_ofReal_iff_of_nonneg
        (add_nonneg dist_nonneg (add_nonneg dist_nonneg dist_nonneg)) |>.mpr
      have hz : dist z.val (0 : ℂ) < r := z.property
      have hw : dist w.val (0 : ℂ) < r := w.property
      linarith
    have comparison := map_edist_le_edist_of_budget Y coincident (C.restore (glue := glue))
      (point Y coincident base) ρ steps (modelTag (θ := θ) z.val) (modelTag (θ := θ) w.val) budget
    apply comparison.trans_eq
    rw [model_edist (pos := pos) (small := small), modelTag_val (θ := θ), modelTag_val (θ := θ)]
    rfl
  have fill_at (z : Metric.ball (0 : ℂ) r) (b : Bool) (y : Metric.eball (origin b) ρ)
      (equal : y.val.val = z.val) :
      fill z = point X glue (C.inverseTag b y) := by
    let p := modelTag (θ := θ) z.val
    let x : Metric.eball (origin p.1) ρ := ⟨p.2,
      (edist_complementarySectorOrigin pos small _ _).trans_lt (model_near z)⟩
    change C.restore (glue := glue) ⟨p.1, x.val⟩ = _
    rw [C.restore_of_near]
    exact shared p.1 b x y ((modelTag_val (θ := θ) z.val).trans equal.symm)
  have center : fill ⟨0, Metric.mem_ball_self rpos⟩ = ctr := by
    let x : Metric.eball (origin false) ρ :=
      ⟨origin false, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr C.positive)⟩
    exact (fill_at _ false x rfl).trans (congrArg (point X glue) (C.inverseTag_center false))
  have representatives (z : Metric.ball (0 : ℂ) r) :
      ∃ b, point X glue b = fill z ∧ C.coordinates b = z.val := by
    let p := modelTag (θ := θ) z.val
    let x : Metric.eball (origin p.1) ρ := ⟨p.2,
      (edist_complementarySectorOrigin pos small _ _).trans_lt (model_near z)⟩
    have equal : x.val.val = z.val := modelTag_val (θ := θ) z.val
    exact ⟨C.inverseTag p.1 x, (fill_at z p.1 x equal).symm,
      (C.coordinates_inverseTag p.1 x).trans equal⟩
  have cover (x : Realization X glue) (near : x ∈ Metric.eball ctr (ENNReal.ofReal r)) :
      ∃ z, fill z = x := by
    obtain ⟨q, rfl⟩ := point_surjective X glue x
    -- Use coverage at the same radius, so the model coordinate still lies in this disk.
    obtain ⟨b, y, rfl, y_near⟩ := near_tags r small_radius q near
    have distance : dist (C.chart b y).val.val 0 < r := by
      have bound := (C.chart_radial b y).trans_lt y_near
      rw [edist_dist] at bound
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp bound
    refine ⟨⟨(C.chart b y).val.val, distance⟩, (fill_at _ b (C.chart b y) rfl).trans ?_⟩
    rw [inverseTag, (C.chart b).symm_apply_apply]
  obtain ⟨chart, _⟩ := ball_isometry_of_local_steps X glue (a false) 0 rpos C.coordinates
    (fun x y hx hy => C.coordinate_step compatible near_tags x y
      (scale ▸ hx) (scale ▸ hy)) fill filling_lipschitz center representatives cover
  exact ⟨r, rpos, 0, ⟨chart.symm⟩⟩

end SectorPairChart
end Unfoldings.MetricGluing
