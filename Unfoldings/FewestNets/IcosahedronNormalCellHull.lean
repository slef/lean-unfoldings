module

public import Unfoldings.FewestNets.IcosahedronFacetNormals
public import Unfoldings.FewestNets.IcosahedronExactFacets
public import Unfoldings.FewestNets.IcosahedronMeshSites
public import Unfoldings.Convex.FiniteNormalFan
public import Mathlib.Analysis.LocallyConvex.Separation

/-! The actual site's gnomonic normal cell is the hull of its incident dual vertices. -/

@[expose] public section

noncomputable section

open scoped Topology

namespace Unfoldings.FewestNets.Icosahedron

open Filter InnerProductSpace

theorem mem_meshHull_iff_meshGauge_le_one {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    {x : Space} : x ∈ meshHull q ↔ ∀ t : MeshFace q, meshGauge hq t x ≤ 1 := by
  refine ⟨fun hx t => meshGauge_le_one_of_mem_hull qbig hq t hx, fun bounds => ?_⟩
  obtain ⟨t, ht⟩ := radialMesh_cover hq x
  rw [meshHull_eq_sublevel qbig hq]
  change hullGauge hq x ≤ 1
  rw [hullGauge_eq_meshGauge hq t ht]
  exact bounds t

/-- The incident facet normals, each scaled to have inner product one with the site. -/
def siteIncidentNormalSlice {q : ℕ} (hq : 0 < q) (a : meshSites q) : Set Space :=
  Set.range (fun t : {t : MeshFace q // (a : Space) ∈ Set.range (inscribedCorners t)} =>
    rawFacetNormal hq t.val)

private theorem meshGauge_site_le_one {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t : MeshFace q) (a : meshSites q) : meshGauge hq t (a : Space) ≤ 1 :=
  meshGauge_le_one_of_mem_hull qbig hq t
    (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ a.property))

/-- The cut of a site's normal cone by the height-one plane is the convex hull
of the normalized supporting planes of its incident facets. -/
theorem mem_normalCone_iff_mem_siteIncidentNormalSlice {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (a : meshSites q) (n : Space) (upward : 0 < inner ℝ n (a : Space)) :
    n ∈ finiteHullNormalCone (fun z : meshSites q => (z : Space)) a ↔
      (inner ℝ n (a : Space))⁻¹ • n ∈ convexHull ℝ (siteIncidentNormalSlice hq a) := by
  let u := (a : Space)
  let c := inner ℝ n u
  let m := c⁻¹ • n
  have cp : 0 < c := upward
  have frame : inner ℝ m u = 1 := by
    change inner ℝ (c⁻¹ • n) u = _
    rw [real_inner_smul_left, inv_mul_cancel₀ cp.ne']
  change n ∈ finiteHullNormalCone (fun z : meshSites q => (z : Space)) a ↔
    m ∈ convexHull ℝ (siteIncidentNormalSlice hq a)
  constructor
  · intro support
    have maxHull : ∀ x ∈ meshHull q, inner ℝ m x ≤ 1 := by
      apply show meshHull q ⊆ {x | inner ℝ m x ≤ 1} from ?_
      apply convexHull_min
      · rintro x (rfl | hx)
        · simp
        · let v : meshSites q := ⟨x, hx⟩
          have bd : inner ℝ n x ≤ c := support v
          have scaled := mul_le_mul_of_nonneg_left bd (inv_nonneg.mpr cp.le)
          change inner ℝ (c⁻¹ • n) x ≤ 1
          rw [real_inner_smul_left]
          exact scaled.trans_eq (inv_mul_cancel₀ cp.ne')
      · exact convex_halfSpace_le (innerSL ℝ m).toLinearMap.isLinear _
    by_contra outside
    have compact : IsCompact (convexHull ℝ (siteIncidentNormalSlice hq a)) :=
      (Set.finite_range _).isCompact_convexHull ℝ
    obtain ⟨L, b, below, above⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) compact.isClosed outside
    let d : Space := (toDual ℝ Space).symm L - b • u
    have pairing (y : Space) : inner ℝ y d = L y - b * inner ℝ y u := by
      dsimp only [d]
      rw [inner_sub_right, real_inner_smul_right, real_inner_comm ((toDual ℝ Space).symm L) y,
        toDual_symm_apply]
    have profitable : 0 < inner ℝ m d := by
      rw [pairing, frame, mul_one]
      exact sub_pos.mpr above
    have each (t : MeshFace q) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), meshGauge hq t (u + δ • d) ≤ 1 := by
      by_cases active : u ∈ Set.range (inscribedCorners t)
      · have value : meshGauge hq t u = 1 := (meshGauge_corner_eq_iff qbig hq t a).mpr active
        have test : rawFacetNormal hq t ∈ siteIncidentNormalSlice hq a :=
          ⟨⟨t, active⟩, rfl⟩
        have converges : meshGauge hq t d < 0 := by
          rw [← inner_rawFacetNormal, pairing, inner_rawFacetNormal, value, mul_one]
          exact sub_neg.mpr (below _ (subset_convexHull ℝ _ test))
        filter_upwards [self_mem_nhdsWithin] with δ pos
        change 0 < δ at pos
        rw [map_add, map_smul, value, smul_eq_mul]
        linarith only [mul_neg_of_pos_of_neg pos converges]
      · have strict : meshGauge hq t u < 1 :=
          lt_of_le_of_ne (meshGauge_site_le_one qbig hq t a)
            ((meshGauge_corner_eq_iff qbig hq t a).not.mpr active)
        have continuous : Continuous (fun δ : ℝ => meshGauge hq t (u + δ • d)) := by
          rw [show (fun δ : ℝ => meshGauge hq t (u + δ • d)) =
              fun δ : ℝ => meshGauge hq t u + δ * meshGauge hq t d by
            funext δ
            rw [map_add, map_smul, smul_eq_mul]]
          fun_prop
        have start : meshGauge hq t (u + (0 : ℝ) • d) < 1 := by
          simpa only [zero_smul, add_zero] using strict
        have near : ∀ᶠ δ in 𝓝 (0 : ℝ), meshGauge hq t (u + δ • d) < 1 :=
          (isOpen_lt continuous continuous_const).mem_nhds start
        exact (near.filter_mono nhdsWithin_le_nhds).mono (fun _ lt => lt.le)
    obtain ⟨δ, all, pos⟩ := ((Filter.eventually_all.mpr each).and self_mem_nhdsWithin).exists
    change 0 < δ at pos
    have inside := (mem_meshHull_iff_meshGauge_le_one qbig hq).mpr all
    have contradict := maxHull (u + δ • d) inside
    rw [inner_add_right, real_inner_smul_right, frame] at contradict
    linarith only [contradict, mul_pos pos profitable]
  · intro inside v
    have valid : convexHull ℝ (siteIncidentNormalSlice hq a) ⊆
        {y | inner ℝ y (v : Space) ≤ 1} := by
      apply convexHull_min
      · rintro _ ⟨t, rfl⟩
        rw [Set.mem_ofPred_eq, inner_rawFacetNormal]
        exact meshGauge_site_le_one qbig hq t.val v
      · have test := convex_halfSpace_le (innerSL ℝ (v : Space)).toLinearMap.isLinear 1
        simpa only [ContinuousLinearMap.coe_coe, innerSL_apply_apply, real_inner_comm] using test
    have cmp : inner ℝ m (v : Space) ≤ 1 := valid inside
    change inner ℝ (c⁻¹ • n) (v : Space) ≤ 1 at cmp
    rw [real_inner_smul_left] at cmp
    change inner ℝ n (v : Space) ≤ c
    have scaled := mul_le_mul_of_nonneg_left cmp cp.le
    rwa [← mul_assoc, mul_inv_cancel₀ cp.ne', one_mul, mul_one] at scaled

end Unfoldings.FewestNets.Icosahedron
