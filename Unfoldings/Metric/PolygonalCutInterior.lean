module

public import Unfoldings.Metric.PolygonalCutLocal
public import Unfoldings.Metric.ConvexLocalLipschitz

/-! Canonical interior lifts and exact convex-region distances when cuts avoid the interior. -/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace Unfoldings.MetricGluing

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite I]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i)) (cuts : Set E) {s : Set E}

/-- Choose an actual cell copy of a physical point. Off the cuts, all choices agree. -/
def cutFromSubtype (cover : s = ⋃ i, cells i) (x : s) : PolygonalCut cells closed cuts := by
  have present : ∃ i, x.val ∈ cells i := Set.mem_iUnion.mp (cover ▸ x.property)
  exact of (fun i => cells i) (cutSeams cells closed cuts).relation present.choose
    ⟨x.val, present.choose_spec⟩

theorem cutToPolygonal_cutFromSubtype (convex : ∀ i, Convex ℝ (cells i))
    (cover : s = ⋃ i, cells i) (x : s) :
    cutToPolygonal cells closed cuts convex cover (cutFromSubtype cells closed cuts cover x) =
      PolygonalPoint.ofSubtype x := by
  apply PolygonalPoint.ext
  rfl

omit [NormedSpace ℝ E] in
/-- An uncut physical point has its specified original cell copy, independently of the selector. -/
theorem cutFromSubtype_eq_of_mem (cover : s = ⋃ i, cells i) (x : s)
    (outside : x.val ∉ cuts) (i : I) (member : x.val ∈ cells i) :
    cutFromSubtype cells closed cuts cover x =
      of (fun i => cells i) (cutSeams cells closed cuts).relation i ⟨x.val, member⟩ := by
  unfold cutFromSubtype
  exact cutSeams_point_eq_of_physical_eq cells closed cuts rfl outside

/-- On a convex physical region the intrinsic uncut metric is the ambient metric. -/
theorem convex_ofSubtype_isometry (convex : Convex ℝ s) :
    Isometry (PolygonalPoint.ofSubtype (s := s)) :=
  PolygonalPoint.includeConvex_isometry s convex (Set.Subset.refl s)

/-- A whole-ball restoration chart gives the same exact distance for all nearby uncut lifts. -/
theorem exists_cutFromSubtype_ball_isometry (convex : ∀ i, Convex ℝ (cells i))
    (cover : s = ⋃ i, cells i) (convex_s : Convex ℝ s) (cut_closed : IsClosed cuts)
    (x : s) (outside : x.val ∉ cuts) :
    ∃ r : ℝ, 0 < r ∧ ∀ y z : s, dist y x < r → dist z x < r →
      y.val ∉ cuts → z.val ∉ cuts →
      edist (cutFromSubtype cells closed cuts cover y) (cutFromSubtype cells closed cuts cover z) =
        edist y z := by
  let f := cutFromSubtype cells closed cuts cover
  obtain ⟨a, represents⟩ := point_surjective (fun i => cells i)
    (cutSeams cells closed cuts).relation (f x)
  have physical : a.2.val = x.val := by
    have equal := congrArg (fun z => (cutToPolygonal cells closed cuts convex cover z).val)
      represents
    change a.2.val =
      (cutToPolygonal cells closed cuts convex cover (cutFromSubtype cells closed cuts cover x)).val
      at equal
    rwa [cutToPolygonal_cutFromSubtype] at equal
  have result := exists_cutToPolygonal_ball_isometry cells closed cuts
    convex cover cut_closed a (by rwa [physical])
  rw [represents] at result
  obtain ⟨r, positive, B, agrees⟩ := result
  have center : cutToPolygonal cells closed cuts convex cover (f x) =
      PolygonalPoint.ofSubtype x := cutToPolygonal_cutFromSubtype cells closed cuts convex cover x
  have lift_near (y : s) (near : dist y x < r) (uncut : y.val ∉ cuts) :
      ∃ w : Metric.eball (f x) (ENNReal.ofReal r), w.val = f y := by
    let target : Metric.eball (cutToPolygonal cells closed cuts convex cover (f x))
        (ENNReal.ofReal r) := ⟨PolygonalPoint.ofSubtype y, by
      change edist (PolygonalPoint.ofSubtype y)
        (cutToPolygonal cells closed cuts convex cover (f x)) < ENNReal.ofReal r
      rw [center, (convex_ofSubtype_isometry convex_s).edist_eq, edist_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr near⟩
    refine ⟨B.symm target, ?_⟩
    apply cutToPolygonal_injective_off_cuts cells closed cuts convex cover
    · have equal := agrees (B.symm target)
      rw [B.apply_symm_apply] at equal
      exact equal.symm.trans (cutToPolygonal_cutFromSubtype cells closed cuts convex cover y).symm
    · have equal := agrees (B.symm target)
      rw [B.apply_symm_apply] at equal
      change (cutToPolygonal cells closed cuts convex cover (B.symm target).val).val ∉ cuts
      rw [← equal]
      exact uncut
  refine ⟨r, positive, ?_⟩
  intro y z hy hz uy uz
  obtain ⟨v, hv⟩ := lift_near y hy uy
  obtain ⟨w, hw⟩ := lift_near z hz uz
  have equality := B.isometry.edist_eq v w
  change edist (B v).val (B w).val = edist v.val w.val at equality
  rw [agrees v, agrees w, hv, hw,
    cutToPolygonal_cutFromSubtype, cutToPolygonal_cutFromSubtype,
    (convex_ofSubtype_isometry convex_s).edist_eq] at equality
  exact equality.symm


/-- Canonical actual lifts of all physical interior points. -/
def cutFromInterior (cover : s = ⋃ i, cells i) (x : interior s) : PolygonalCut cells closed cuts :=
  cutFromSubtype cells closed cuts cover ⟨x.val, interior_subset x.property⟩

/-- The canonical interior lift preserves every distance in a convex region avoiding the cuts. -/
theorem cutFromInterior_isometry (convex : ∀ i, Convex ℝ (cells i))
    (cover : s = ⋃ i, cells i) (convex_s : Convex ℝ s) (cut_closed : IsClosed cuts)
    (outside : Disjoint (interior s) cuts) :
    Isometry (cutFromInterior cells closed cuts cover) := by
  have uncut (x : interior s) : x.val ∉ cuts :=
    fun member => Set.disjoint_left.mp outside x.property member
  have bounded : LipschitzWith 1 (cutFromInterior cells closed cuts cover) := by
    apply convex_subtype_emetric_lipschitzWith_of_local (interior s) convex_s.interior
    intro x
    obtain ⟨r, positive, local_bound⟩ := exists_cutFromSubtype_ball_isometry cells closed cuts
      convex cover convex_s cut_closed ⟨x.val, interior_subset x.property⟩ (uncut x)
    refine ⟨r, positive, ?_⟩
    intro y hy z hz
    simp only [ENNReal.coe_one, one_mul]
    exact (local_bound ⟨y.val, interior_subset y.property⟩
      ⟨z.val, interior_subset z.property⟩ hy hz (uncut y) (uncut z)).le
  intro x y
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using bounded x y
  · have bound := cutToPolygonal_lipschitz cells closed cuts convex cover
      (cutFromInterior cells closed cuts cover x)
      (cutFromInterior cells closed cuts cover y)
    change edist (cutToPolygonal cells closed cuts convex cover
      (cutFromSubtype cells closed cuts cover ⟨x.val, interior_subset x.property⟩))
      (cutToPolygonal cells closed cuts convex cover
        (cutFromSubtype cells closed cuts cover ⟨y.val, interior_subset y.property⟩)) ≤ _ at bound
    rw [cutToPolygonal_cutFromSubtype, cutToPolygonal_cutFromSubtype,
      (convex_ofSubtype_isometry convex_s).edist_eq] at bound
    simpa only [Subtype.edist_eq, ENNReal.coe_one, one_mul] using bound

end Unfoldings.MetricGluing
