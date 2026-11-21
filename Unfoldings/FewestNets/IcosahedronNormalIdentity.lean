module

public import Unfoldings.FewestNets.IcosahedronDualArc
public import Unfoldings.FewestNets.IcosahedronMeshFaceIdentity

/-! The outward unit normals distinguish the individual fine facets. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

private theorem corner_range_subset_of_facetNormal_eq {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t s : MeshFace q) (eq : facetNormal hq t = facetNormal hq s) :
    Set.range (inscribedCorners t) ⊆ Set.range (inscribedCorners s) := by
  rintro _ ⟨k, rfl⟩
  let a : meshSites q := ⟨inscribedCorners t k, ⟨(t, k), rfl⟩⟩
  let b : meshSites q := ⟨inscribedCorners s 0, ⟨(s, 0), rfl⟩⟩
  have ha : (a : Space) ∈ Set.range (inscribedCorners t) := Set.mem_range_self k
  have bound := bound_facetNormal_of_corner qbig hq t a ha b
  rw [eq, inner_facetNormal, inner_facetNormal] at bound
  change meshGauge hq s (inscribedCorners s 0) / ‖rawFacetNormal hq s‖ ≤
    meshGauge hq s (a : Space) / ‖rawFacetNormal hq s‖ at bound
  rw [meshGauge_corner] at bound
  have lower := (div_le_div_iff_of_pos_right
    (norm_pos_iff.mpr (rawFacetNormal_ne_zero hq s))).mp bound
  have upper := meshGauge_le_one_of_mem_hull qbig hq s
    (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ a.property))
  exact (meshGauge_corner_eq_iff qbig hq s a).mp (le_antisymm upper lower)

/-- The outward unit normal uniquely identifies the fine icosahedral face. -/
theorem facetNormal_injective {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q) :
    Function.Injective (facetNormal hq) := by
  intro t s eq
  exact meshFace_eq_of_corner_range_eq hq t s (Set.Subset.antisymm
    (corner_range_subset_of_facetNormal_eq qbig hq t s eq)
    (corner_range_subset_of_facetNormal_eq qbig hq s t eq.symm))

theorem facetNormal_add_ne_zero_of_shared_corner {q : ℕ} (hq : 0 < q) (t s : MeshFace q)
    {a : Space} (at_t : a ∈ Set.range (inscribedCorners t))
    (at_s : a ∈ Set.range (inscribedCorners s)) : facetNormal hq t + facetNormal hq s ≠ 0 := by
  have first : 0 < inner ℝ (facetNormal hq t) a := by
    obtain ⟨i, eq⟩ := at_t
    rw [← eq]
    exact inner_facetNormal_corner_pos hq t i
  have second : 0 < inner ℝ (facetNormal hq s) a := by
    obtain ⟨j, eq⟩ := at_s
    rw [← eq]
    exact inner_facetNormal_corner_pos hq s j
  intro zero
  have h := congrArg (fun x => inner ℝ x a) zero
  rw [inner_add_left, inner_zero_left] at h
  linarith only [h, first, second]

end Unfoldings.FewestNets.Icosahedron
