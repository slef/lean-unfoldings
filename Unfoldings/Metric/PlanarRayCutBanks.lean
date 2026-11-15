module

public import Unfoldings.Metric.AffineHalfspaceBankSeparation
public import Unfoldings.Geometry.SegmentInequalities
public import Unfoldings.Geometry.RayForwardHalfspace

/-! The two whole banks of a planar slit ray, with their exact common endpoint. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.MetricGluing

/-- The actual full nonnegative geometric ray, including its source. -/
def rayCut (p q : Plane) : Set Plane :=
  Set.range (fun t : ℝ≥0 => AffineMap.lineMap p q (t : ℝ))

theorem isClosed_rayCut (p q : Plane) : IsClosed (rayCut p q) := by
  rw [rayCut, ray_eq_closedChamber]
  exact AffineArrangement.isClosed_closedChamber _ _

theorem rayCut_on_line (p q : Plane) : ∀ x ∈ rayCut p q, orientMap p q x = 0 := by
  rintro x ⟨t, rfl⟩
  simp only [orientMap_apply, orient_lineMap]

theorem lineMap_not_mem_rayCut {p q : Plane} (different : p ≠ q) {t : ℝ} (negative : t < 0) :
    AffineMap.lineMap p q t ∉ rayCut p q := by
  rintro ⟨s, equal⟩
  have parameters := congrArg (lineCoordinate p q) equal
  rw [lineCoordinate_lineMap different, lineCoordinate_lineMap different] at parameters
  exact (not_lt_of_ge (parameters ▸ s.coe_nonneg)) negative

variable {I : Type*} [Finite I] (cells : I → Set Plane) (closed : ∀ i, IsClosed (cells i))
  (convex : ∀ i, Convex ℝ (cells i)) (full : ∀ i, (interior (cells i)).Nonempty)
  (cover : (⋃ i, cells i) = Set.univ) (p q : Plane) (different : p ≠ q)
  (signs : I → Bool)
  (aligned : ∀ i x, x ∈ cells i → 0 ≤ AffineArrangement.signed (orientMap p q) (signs i) x)

/-- A canonical actual bank point on the entire supporting line, allowing negative time.
Both sides will agree before the cut begins and at its source. -/
def rayCutBankPoint (side : Bool) (t : ℝ) : PolygonalCut cells closed (rayCut p q) :=
  affineHalfspaceBank cells closed convex full cover (orientMap p q) (orientMap_ne_zero different)
    signs aligned side (AffineArrangement.exists_signed_pos_of_zero (orientMap p q)
      (orientMap_ne_zero different) (p := p)
      (by simp only [orientMap_apply, orient_self_left]) side)
    (rayCut p q) (isClosed_rayCut p q) (rayCut_on_line p q)
    ⟨AffineMap.lineMap p q t, by
      change 0 ≤ AffineArrangement.signed (orientMap p q) side (AffineMap.lineMap p q t)
      simp only [AffineArrangement.signed_apply, orientMap_apply, orient_lineMap,
        neg_zero, ite_self, le_refl]⟩

@[simp] theorem fold_rayCutBankPoint (side : Bool) (t : ℝ) :
    (cutSeams cells closed (rayCut p q)).fold
      (rayCutBankPoint cells closed convex full cover p q different signs aligned side t) =
        AffineMap.lineMap p q t :=
  fold_affineHalfspaceBank cells closed convex full cover (orientMap p q)
    (orientMap_ne_zero different) signs aligned side _ (rayCut p q)
    (isClosed_rayCut p q) (rayCut_on_line p q) _

/-- Every same-side bank distance is the original Euclidean line distance. -/
theorem edist_rayCutBankPoint (side : Bool) (s t : ℝ) :
    edist (rayCutBankPoint cells closed convex full cover p q different signs aligned side s)
      (rayCutBankPoint cells closed convex full cover p q different signs aligned side t) =
        edist (AffineMap.lineMap p q s) (AffineMap.lineMap p q t) :=
  affineHalfspaceBank_isometry cells closed convex full cover (orientMap p q)
    (orientMap_ne_zero different) signs aligned side _ (rayCut p q)
    (isClosed_rayCut p q) (rayCut_on_line p q) _ _

theorem continuous_rayCutBankPoint (side : Bool) :
    Continuous (rayCutBankPoint cells closed convex full cover p q different signs aligned
      side) := by
  have bounded : LipschitzWith (nndist p q)
      (rayCutBankPoint cells closed convex full cover p q different signs aligned side) := by
    intro s t
    rw [edist_rayCutBankPoint]
    exact lipschitzWith_lineMap p q s t
  exact bounded.continuous

/-- Before the slit starts, its canonical two-sided copies are identical. -/
theorem rayCutBankPoint_eq_of_neg {t : ℝ} (negative : t < 0) :
    rayCutBankPoint cells closed convex full cover p q different signs aligned true t =
      rayCutBankPoint cells closed convex full cover p q different signs aligned false t := by
  apply affineHalfspaceBanks_eq_off_cuts cells closed convex full cover (orientMap p q)
    (orientMap_ne_zero different) signs aligned true _ (rayCut p q)
    (isClosed_rayCut p q) (rayCut_on_line p q) false _ _ _ rfl
  exact lineMap_not_mem_rayCut different negative

/-- The two actual metric banks have the same source endpoint. -/
theorem rayCutBankPoint_zero :
    rayCutBankPoint cells closed convex full cover p q different signs aligned true 0 =
      rayCutBankPoint cells closed convex full cover p q different signs aligned false 0 := by
  have closed_equal : IsClosed {t : ℝ |
      rayCutBankPoint cells closed convex full cover p q different signs aligned true t =
        rayCutBankPoint cells closed convex full cover p q different signs aligned false t} :=
    isClosed_eq (continuous_rayCutBankPoint cells closed convex full cover p q different signs
      aligned true) (continuous_rayCutBankPoint cells closed convex full cover p q different signs
      aligned false)
  have negative_subset : Set.Iio (0 : ℝ) ⊆ {t : ℝ |
      rayCutBankPoint cells closed convex full cover p q different signs aligned true t =
        rayCutBankPoint cells closed convex full cover p q different signs aligned false t} :=
    fun _ negative => rayCutBankPoint_eq_of_neg cells closed convex full cover p q different signs
      aligned negative
  apply closed_equal.closure_subset (closure_mono negative_subset ?_)
  rw [closure_Iio]
  exact le_rfl

/-- Every strictly positive point has two distinct actual metric bank copies. -/
theorem rayCutBankPoint_ne_of_pos {s t : ℝ} (positive : 0 < s) :
    rayCutBankPoint cells closed convex full cover p q different signs aligned true s ≠
      rayCutBankPoint cells closed convex full cover p q different signs aligned false t := by
  let pos (side : Bool) : ∃ z, 0 < AffineArrangement.signed (orientMap p q) side z :=
    AffineArrangement.exists_signed_pos_of_zero (orientMap p q) (orientMap_ne_zero different)
      (p := p) (by simp only [orientMap_apply, orient_self_left]) side
  let x : {x | 0 ≤ AffineArrangement.signed (orientMap p q) true x} :=
    ⟨AffineMap.lineMap p q s, by simp [AffineArrangement.signed, orient_lineMap]⟩
  let y : {x | 0 ≤ AffineArrangement.signed (orientMap p q) false x} :=
    ⟨AffineMap.lineMap p q t, by simp [AffineArrangement.signed, orient_lineMap]⟩
  have local_cut : ∀ z ∈ rayForwardHalfspace p q, orientMap p q z = 0 → z ∈ rayCut p q := by
    intro z forward zero
    obtain ⟨u, hu, rfl⟩ := exists_positive_ray_parameter different forward zero
    exact ⟨⟨u, hu.le⟩, rfl⟩
  exact affineHalfspaceBanks_ne_of_local_cut cells closed convex full cover (orientMap p q)
    (orientMap_ne_zero different) signs aligned true (pos true) (rayCut p q)
    (isClosed_rayCut p q) (rayCut_on_line p q) false (pos false) (by decide)
    (isOpen_rayForwardHalfspace p q) local_cut x y
    (lineMap_mem_rayForwardHalfspace different positive)

/-- The exact two-copy rule: copies agree on the uncut continuation and its endpoint only. -/
theorem rayCutBankPoint_eq_iff (t : ℝ) :
    (rayCutBankPoint cells closed convex full cover p q different signs aligned true t =
      rayCutBankPoint cells closed convex full cover p q different signs aligned false t) ↔
        t ≤ 0 := by
  constructor
  · intro equal
    by_contra positive
    exact rayCutBankPoint_ne_of_pos cells closed convex full cover p q different signs aligned
      (lt_of_not_ge positive) equal
  · intro nonpositive
    rcases nonpositive.lt_or_eq with negative | rfl
    · exact rayCutBankPoint_eq_of_neg cells closed convex full cover p q different signs aligned
        negative
    · exact rayCutBankPoint_zero cells closed convex full cover p q different signs aligned


/-- Across the two banks, equal metric points have the same nonpositive line parameter. -/
theorem rayCutBankPoint_eq_iff_parameters (s t : ℝ) :
    (rayCutBankPoint cells closed convex full cover p q different signs aligned true s =
      rayCutBankPoint cells closed convex full cover p q different signs aligned false t) ↔
        s = t ∧ s ≤ 0 := by
  constructor
  · intro equal
    have same := congrArg
      (fun z => lineCoordinate p q ((cutSeams cells closed (rayCut p q)).fold z)) equal
    rw [fold_rayCutBankPoint, fold_rayCutBankPoint, lineCoordinate_lineMap different,
      lineCoordinate_lineMap different] at same
    refine ⟨same, ?_⟩
    apply (rayCutBankPoint_eq_iff cells closed convex full cover p q different signs aligned s).mp
    simpa only [← same] using equal
  · rintro ⟨rfl, nonpositive⟩
    exact (rayCutBankPoint_eq_iff cells closed convex full cover p q different signs aligned _).mpr
      nonpositive

/-- Each entire line bank is closed and embedded, with no extra limit at infinity. -/
theorem rayCutBankPoint_isClosedEmbedding (side : Bool) :
    Topology.IsClosedEmbedding
      (rayCutBankPoint cells closed convex full cover p q different signs aligned side) := by
  have bounded : LipschitzWith (nndist p q)
      (rayCutBankPoint cells closed convex full cover p q different signs aligned side) := by
    intro s t
    rw [edist_rayCutBankPoint]
    exact lipschitzWith_lineMap p q s t
  have lower : AntilipschitzWith (nndist p q)⁻¹
      (rayCutBankPoint cells closed convex full cover p q different signs aligned side) := by
    intro s t
    rw [edist_rayCutBankPoint]
    exact antilipschitzWith_lineMap different s t
  exact lower.isClosedEmbedding bounded.uniformContinuous

/-- The actual whole positive bank, with its source, is closed and embedded. -/
theorem rayCutPositiveBank_isClosedEmbedding (side : Bool) :
    Topology.IsClosedEmbedding (fun t : ℝ≥0 =>
      rayCutBankPoint cells closed convex full cover p q different signs aligned side (t : ℝ)) :=
  (rayCutBankPoint_isClosedEmbedding cells closed convex full cover p q different signs aligned
    side).comp NNReal.isClosedEmbedding_coe

/-- The two complete positive banks meet at exactly their actual common source. -/
theorem rayCutPositiveBanks_inter :
    Set.range (fun t : ℝ≥0 =>
      rayCutBankPoint cells closed convex full cover p q different signs aligned true (t : ℝ)) ∩
    Set.range (fun t : ℝ≥0 =>
      rayCutBankPoint cells closed convex full cover p q different signs aligned false (t : ℝ)) =
      {rayCutBankPoint cells closed convex full cover p q different signs aligned true 0} := by
  ext z
  constructor
  · rintro ⟨⟨s, rfl⟩, ⟨t, equal⟩⟩
    have nonpositive := ((rayCutBankPoint_eq_iff_parameters cells closed convex full cover p q
      different signs aligned s t).mp equal.symm).2
    have zero : (s : ℝ) = 0 := le_antisymm nonpositive s.coe_nonneg
    change rayCutBankPoint cells closed convex full cover p q different signs aligned true
      (s : ℝ) ∈ {rayCutBankPoint cells closed convex full cover p q different signs aligned true 0}
    rw [zero]
    exact Set.mem_singleton _
  · rintro rfl
    exact ⟨⟨0, rfl⟩, ⟨0, (rayCutBankPoint_zero cells closed convex full cover p q different signs
      aligned).symm⟩⟩

end Unfoldings.MetricGluing
