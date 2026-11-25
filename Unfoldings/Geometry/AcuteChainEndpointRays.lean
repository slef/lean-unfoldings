module

public import Unfoldings.Geometry.AcuteChainClosure
public import Unfoldings.Geometry.SegmentVertices

/-! The trimmed acute chain and both closing links have the expected endpoint rays. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

open Filter Topology

variable {n : ℕ} (P : PolygonalChain Plane (n + 1))

theorem eventually_mem_linear_path_iff_initial_ray (h : Plane →L[ℝ] ℝ)
    (progress : ∀ i, 0 < h (P.edge i)) :
    ∀ᶠ z in 𝓝 (P.vertex 0), z ∈ Set.range P.path ↔
      z - P.vertex 0 ∈ nonnegativeRay (P.edge 0) := by
  have injective : Function.Injective P.vertex := fun _ _ same =>
    (P.strictMono_linear_vertices h progress).injective (congrArg h same)
  have near := eventually_mem_segment_family_iff_incident_rays
    (fun i : Fin (n + 1) => P.vertex i.castSucc) (fun i => P.vertex i.succ)
    (P.vertex 0) (P.vertex_not_mem_openSegment_of_linear_progress h progress 0)
  have at_first (i : Fin (n + 1)) : P.vertex 0 = P.vertex i.castSucc ↔ i = 0 := by
    constructor
    · intro same
      exact Fin.ext (congrArg Fin.val (injective same)).symm
    · rintro rfl
      rfl
  have not_last (i : Fin (n + 1)) : P.vertex 0 ≠ P.vertex i.succ := by
    intro same
    have values := congrArg Fin.val (injective same)
    change 0 = i.val + 1 at values
    omega
  have model : segmentIncidentRays (fun i : Fin (n + 1) => P.vertex i.castSucc)
      (fun i => P.vertex i.succ) (P.vertex 0) = nonnegativeRay (P.edge 0) := by
    classical
    simp only [segmentIncidentRays]
    simp_rw [at_first, ite_eq_right (not_last _), Set.union_empty]
    simp [Set.iUnion_ite, edge]
  filter_upwards [near] with z local_model
  have initial_on_segment : P.vertex 0 ∈ ⋃ i : Fin (n + 1),
      segment ℝ (P.vertex i.castSucc) (P.vertex i.succ) :=
    Set.mem_iUnion.mpr ⟨0, left_mem_segment ℝ _ _⟩
  rw [P.path_range_eq_segments, Set.union_eq_right.mpr (Set.singleton_subset_iff.mpr
    initial_on_segment)]
  simpa only [model] using local_model

theorem eventually_mem_linear_path_iff_terminal_ray (h : Plane →L[ℝ] ℝ)
    (progress : ∀ i, 0 < h (P.edge i)) :
    let last := Fin.last (n + 1)
    ∀ᶠ z in 𝓝 (P.vertex last), z ∈ Set.range P.path ↔
      z - P.vertex last ∈ nonnegativeRay (-P.edge (Fin.last n)) := by
  let last := Fin.last (n + 1)
  have injective : Function.Injective P.vertex := fun _ _ same =>
    (P.strictMono_linear_vertices h progress).injective (congrArg h same)
  have near := eventually_mem_segment_family_iff_incident_rays
    (fun i : Fin (n + 1) => P.vertex i.castSucc) (fun i => P.vertex i.succ)
    (P.vertex last) (P.vertex_not_mem_openSegment_of_linear_progress h progress last)
  have not_first (i : Fin (n + 1)) : P.vertex last ≠ P.vertex i.castSucc := by
    intro same
    have values := congrArg Fin.val (injective same)
    change n + 1 = i.val at values
    omega
  have at_last (i : Fin (n + 1)) : P.vertex last = P.vertex i.succ ↔ i = Fin.last n := by
    constructor
    · intro same
      have values := congrArg Fin.val (injective same)
      change n + 1 = i.val + 1 at values
      exact Fin.ext (by change i.val = n; omega)
    · rintro rfl
      rw [Fin.succ_last]
  have model : segmentIncidentRays (fun i : Fin (n + 1) => P.vertex i.castSucc)
      (fun i => P.vertex i.succ) (P.vertex last) =
        nonnegativeRay (-P.edge (Fin.last n)) := by
    classical
    simp only [segmentIncidentRays]
    simp_rw [ite_eq_right (not_first _), at_last, Set.empty_union]
    simp only [Set.iUnion_ite, edge, neg_sub, Fin.succ_last, last]
    simp
  change ∀ᶠ z in 𝓝 (P.vertex last), _
  filter_upwards [near, isClosed_singleton.isOpen_compl.mem_nhds
    (not_first (0 : Fin (n + 1)))] with z local_model away_start
  change z ∉ ({P.vertex 0} : Set Plane) at away_start
  rw [P.path_range_eq_segments]
  simpa only [Set.mem_union, away_start, false_or, model] using local_model

variable (c : Plane) (h k : Plane →L[ℝ] ℝ)

/-- Near the first trim there is only the forward bank and the initial connector. -/
theorem eventually_mem_twoLinkClosure_iff_initial_rays
    (progress : ∀ i, 0 < k (P.edge i)) (terminal : k (P.vertex (Fin.last (n + 1))) ≤ k c) :
    ∀ᶠ z in 𝓝 (P.vertex 0), z ∈ P.twoLinkClosure c ↔
      z - P.vertex 0 ∈ nonnegativeRay (P.edge 0) ∪ nonnegativeRay (c - P.vertex 0) := by
  let a := P.vertex 0
  let b := P.vertex (Fin.last (n + 1))
  have different : k a < k b :=
    P.strictMono_linear_vertices k progress (by exact Nat.succ_pos n)
  have away_terminal : a ∉ segment ℝ b c := by
    intro member
    have value : k.toLinearMap.toAffineMap a ∈ segment ℝ
        (k.toLinearMap.toAffineMap b) (k.toLinearMap.toAffineMap c) :=
      (image_segment ℝ k.toLinearMap.toAffineMap _ _).subset (Set.mem_image_of_mem _ member)
    change k a ∈ segment ℝ (k b) (k c) at value
    rw [segment_eq_Icc terminal] at value
    exact different.not_ge value.1
  have local_bank := P.eventually_mem_linear_path_iff_initial_ray k progress
  have local_link := eventually_mem_segment_iff_nonnegativeRay a c
  filter_upwards [local_bank, local_link,
    (compact_segment b c).isClosed.isOpen_compl.mem_nhds away_terminal] with z bank link absent
  change z ∉ segment ℝ b c at absent
  change (z ∈ Set.range P.path ∨ z ∈ segment ℝ b c ∨ z ∈ segment ℝ c a) ↔
    z - a ∈ nonnegativeRay (P.edge 0) ∪ nonnegativeRay (c - a)
  simp only [Set.mem_union, absent, false_or, bank, segment_symm ℝ c a, link]
  rfl

/-- Near the last trim there is only the backward bank and the terminal connector. -/
theorem eventually_mem_twoLinkClosure_iff_terminal_rays
    (progress : ∀ i, 0 < h (P.edge i)) (initial : h c ≤ h (P.vertex 0)) :
    let b := P.vertex (Fin.last (n + 1))
    ∀ᶠ z in 𝓝 b, z ∈ P.twoLinkClosure c ↔
      z - b ∈ nonnegativeRay (-P.edge (Fin.last n)) ∪ nonnegativeRay (c - b) := by
  let a := P.vertex 0
  let b := P.vertex (Fin.last (n + 1))
  have different : h a < h b :=
    P.strictMono_linear_vertices h progress (by exact Nat.succ_pos n)
  have away_initial : b ∉ segment ℝ c a := by
    intro member
    have value : h.toLinearMap.toAffineMap b ∈ segment ℝ
        (h.toLinearMap.toAffineMap c) (h.toLinearMap.toAffineMap a) :=
      (image_segment ℝ h.toLinearMap.toAffineMap _ _).subset (Set.mem_image_of_mem _ member)
    change h b ∈ segment ℝ (h c) (h a) at value
    rw [segment_eq_Icc initial] at value
    exact different.not_ge value.2
  have local_bank := P.eventually_mem_linear_path_iff_terminal_ray h progress
  have local_link := eventually_mem_segment_iff_nonnegativeRay b c
  change ∀ᶠ z in 𝓝 b, _
  filter_upwards [local_bank, local_link,
    (compact_segment c a).isClosed.isOpen_compl.mem_nhds away_initial] with z bank link absent
  change z ∉ segment ℝ c a at absent
  change (z ∈ Set.range P.path ∨ z ∈ segment ℝ b c ∨ z ∈ segment ℝ c a) ↔
    z - b ∈ nonnegativeRay (-P.edge (Fin.last n)) ∪ nonnegativeRay (c - b)
  simp only [Set.mem_union, absent, or_false, bank, link]
  rfl

end Unfoldings.PolygonalChain
