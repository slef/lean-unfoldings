module

public import Unfoldings.FewestNets.LatitudeAnnularSupport
public import Unfoldings.FewestNets.LatitudeChordBase
public import Unfoldings.FewestNets.LatitudeMidpointSweep
public import Unfoldings.Geometry.AffineSupportBoundary

/-! Every actual triangle from the latitude sweep lies on the sampled convex hull. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- The sampled poles and periodically indexed row sites. -/
def latitudeSites (a : ℝ) : Set Space :=
  {latitudeSite 0 0, latitudeSite π 0} ∪
    {p | ∃ j ≤ latitudeStripCount a, ∃ k, p = latitudeRowSite a j k}

theorem latitudeRowSite_mem_sites (a : ℝ) {j : ℕ} (valid : j ≤ latitudeStripCount a) (k : ℕ) :
    latitudeRowSite a j k ∈ latitudeSites a :=
  Or.inr ⟨j, valid, k, rfl⟩

/-- A common supporting affine level puts the entire chord triangle on
the boundary of the sampled convex hull. -/
theorem convexHull_subset_frontier_of_latitudeSupport {a : ℝ} {triangle : Set Space}
    (vertices : triangle ⊆ latitudeSites a) (ell longitude d : ℝ)
    (upper : ∀ p ∈ latitudeSites a, inner ℝ (latitudeSite ell longitude) p ≤ d)
    (equal : ∀ p ∈ triangle, inner ℝ (latitudeSite ell longitude) p = d) :
    convexHull ℝ triangle ⊆ frontier (convexHull ℝ (latitudeSites a)) := by
  let n := latitudeSite ell longitude
  let form := (innerSL ℝ n).toLinearMap
  let f : Space →ᵃ[ℝ] ℝ := AffineMap.const ℝ Space d - form.toAffineMap
  have proper : f ≠ 0 := by
    intro zero
    have at_zero := DFunLike.congr_fun zero (0 : Space)
    have at_normal := DFunLike.congr_fun zero n
    change d - inner ℝ n 0 = 0 at at_zero
    change d - inner ℝ n n = 0 at at_normal
    rw [inner_zero_right, sub_zero] at at_zero
    rw [real_inner_self_eq_norm_sq, latitudeSite_unit] at at_normal
    linarith only [at_zero, at_normal]
  have hull_below := (convex_halfSpace_le form.isLinear d).convexHull_subset_iff.mpr upper
  have hull_level := (convex_hyperplane form.isLinear d).convexHull_subset_iff.mpr equal
  intro p hp
  have in_hull := convexHull_mono vertices hp
  exact ⟨subset_closure in_hull, not_mem_interior_of_affine_lower_bound f proper
    (fun q hq => sub_nonneg.mpr (hull_below hq)) (sub_eq_zero.mpr (hull_level hp).symm)⟩

/-- The lower-row advance is the actual supporting chord triangle of
its two consecutive lower sites and its nearest upper site. -/
theorem latitude_lowerAdvance_support {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (valid : j < latitudeStripCount a) (b : Fin (latitudeRowSize a j)) (apex : ℕ)
    (nearest : |rowMidpoint (latitudeRowSize a j) b - rowLongitude (latitudeRowSize a (j + 1)) apex|
      ≤ π / latitudeRowSize a (j + 1)) :
    convexHull ℝ ({latitudeRowSite a j b.val, latitudeRowSite a j (b.val + 1),
      latitudeRowSite a (j + 1) apex} : Set Space) ⊆ frontier (convexHull ℝ (latitudeSites a)) := by
  let longitude := rowMidpoint (latitudeRowSize a j) b
  obtain ⟨θ, _, same, upper, north, south⟩ := exists_latitudeAnnular_support positive small valid
    longitude b.val apex (rowMidpoint_closest_left b) nearest
  let ell := latitudeStripMid a j - θ
  let d := inner ℝ (latitudeSite ell longitude) (latitudeRowSite a j b.val)
  refine convexHull_subset_frontier_of_latitudeSupport ?_ ell longitude d ?_ ?_
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact latitudeRowSite_mem_sites a valid.le _
    · exact latitudeRowSite_mem_sites a valid.le _
    · exact latitudeRowSite_mem_sites a (Nat.succ_le_of_lt valid) _
  · intro p hp
    rcases hp with pole | ⟨i, row, k, rfl⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at pole
      rcases pole with rfl | rfl
      · simpa only [latitudeSite_north] using north.le
      · simpa only [latitudeSite_south] using south.le
    · exact upper i row k
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · rfl
    · exact (latitudeRowSite_midpoint_support_eq a j b ell).symm
    · exact same.symm

/-- The upper-row advance has the corresponding consecutive upper base
and nearest lower apex, including when the midpoints coincide. -/
theorem latitude_upperAdvance_support {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (valid : j < latitudeStripCount a) (b : Fin (latitudeRowSize a (j + 1))) (apex : ℕ)
    (nearest : |rowMidpoint (latitudeRowSize a (j + 1)) b - rowLongitude (latitudeRowSize a j) apex|
      ≤ π / latitudeRowSize a j) :
    convexHull ℝ ({latitudeRowSite a (j + 1) b.val, latitudeRowSite a (j + 1) (b.val + 1),
      latitudeRowSite a j apex} : Set Space) ⊆ frontier (convexHull ℝ (latitudeSites a)) := by
  let longitude := rowMidpoint (latitudeRowSize a (j + 1)) b
  obtain ⟨θ, _, same, upper, north, south⟩ := exists_latitudeAnnular_support positive small valid
    longitude apex b.val nearest (rowMidpoint_closest_left b)
  let ell := latitudeStripMid a j - θ
  let d := inner ℝ (latitudeSite ell longitude) (latitudeRowSite a j apex)
  have valid₁ := Nat.succ_le_of_lt valid
  refine convexHull_subset_frontier_of_latitudeSupport ?_ ell longitude d ?_ ?_
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact latitudeRowSite_mem_sites a valid₁ _
    · exact latitudeRowSite_mem_sites a valid₁ _
    · exact latitudeRowSite_mem_sites a valid.le _
  · intro p hp
    rcases hp with pole | ⟨i, row, k, rfl⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at pole
      rcases pole with rfl | rfl
      · simpa only [latitudeSite_north] using north.le
      · simpa only [latitudeSite_south] using south.le
    · exact upper i row k
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact same.symm
    · exact (latitudeRowSite_midpoint_support_eq a (j + 1) b ell).symm.trans same.symm
    · rfl

/-- The actual chord triangle picked by one step of the cyclic midpoint sweep. -/
def latitudeSweepChordTriangle (a : ℝ) (j : ℕ)
    (step : Fin (latitudeRowSize a j + latitudeRowSize a (j + 1)) ≃
      Fin (latitudeRowSize a j) ⊕ Fin (latitudeRowSize a (j + 1)))
    (i : Fin (latitudeRowSize a j + latitudeRowSize a (j + 1))) : Set Space :=
  match step i with
  | .inl b => convexHull ℝ {latitudeRowSite a j b.val, latitudeRowSite a j (b.val + 1),
      latitudeRowSite a (j + 1) (rowProgress (upperRank step) i.val)}
  | .inr b => convexHull ℝ {latitudeRowSite a (j + 1) b.val, latitudeRowSite a (j + 1) (b.val + 1),
      latitudeRowSite a j (rowProgress (lowerRank step) i.val)}

/-- The straightened strip is built entirely out of supporting chord triangles. -/
theorem latitudeSweepChordTriangle_subset_frontier {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (valid : j < latitudeStripCount a)
    (step : Fin (latitudeRowSize a j + latitudeRowSize a (j + 1)) ≃
      Fin (latitudeRowSize a j) ⊕ Fin (latitudeRowSize a (j + 1)))
    (sorted : StrictMono (midpointKey ∘ step))
    (i : Fin (latitudeRowSize a j + latitudeRowSize a (j + 1))) :
    latitudeSweepChordTriangle a j step i ⊆ frontier (convexHull ℝ (latitudeSites a)) := by
  unfold latitudeSweepChordTriangle
  rcases advance : step i with b | b
  · exact latitude_lowerAdvance_support positive small valid b _
      (upperSweep_near_lower_midpoint step sorted
        (latitude_row_size_pos positive small (Nat.succ_le_of_lt valid)) i b advance)
  · exact latitude_upperAdvance_support positive small valid b _
      (lowerSweep_near_upper_midpoint step sorted
        (latitude_row_size_pos positive small valid.le) i b advance)

end Unfoldings.FewestNets
