module

public import Unfoldings.Geometry.RadialClosureVertexRays

/-! A radial comparison closure has its actual two incident rays at each bank endpoint. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

open Filter Topology

variable {n : ℕ} (P : PolygonalChain Plane (n + 1)) (q c : Plane)

theorem eventually_mem_radial_path_iff_initial_ray
    (radial : P.RadialFrom q 0) (genuine : ∀ i, P.edge i ≠ 0) :
    ∀ᶠ z in 𝓝 (P.vertex 0), z ∈ Set.range P.path ↔
      z - P.vertex 0 ∈ nonnegativeRay (P.edge 0) := by
  have injective : Function.Injective P.vertex := fun _ _ same =>
    (P.vertex_radius_strictMono_of_radial q radial genuine).injective
      (congrArg (dist q) same)
  have near := eventually_mem_segment_family_iff_incident_rays
    (fun i : Fin (n + 1) => P.vertex i.castSucc) (fun i => P.vertex i.succ)
    (P.vertex 0) (P.vertex_not_mem_openSegment_of_radial q radial genuine 0)
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

theorem eventually_mem_radial_path_iff_terminal_ray
    (radial : P.RadialFrom q 0) (genuine : ∀ i, P.edge i ≠ 0) :
    let last := Fin.last (n + 1)
    ∀ᶠ z in 𝓝 (P.vertex last), z ∈ Set.range P.path ↔
      z - P.vertex last ∈ nonnegativeRay (-P.edge (Fin.last n)) := by
  let last := Fin.last (n + 1)
  have injective : Function.Injective P.vertex := fun _ _ same =>
    (P.vertex_radius_strictMono_of_radial q radial genuine).injective
      (congrArg (dist q) same)
  have near := eventually_mem_segment_family_iff_incident_rays
    (fun i : Fin (n + 1) => P.vertex i.castSucc) (fun i => P.vertex i.succ)
    (P.vertex last) (P.vertex_not_mem_openSegment_of_radial q radial genuine last)
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

/-- The closure has its bank ray and the ray toward the comparison source at the first trim. -/
theorem eventually_mem_radialClosure_iff_initial_rays
    (radial : P.RadialFrom q 0) (genuine : ∀ i, P.edge i ≠ 0)
    (initial : 0 < dist q (P.vertex 0))
    (progress : dist q (P.vertex 0) < dist q (P.vertex (Fin.last (n + 1))))
    (height : Plane →ₗ[ℝ] ℝ) (supported : ∀ z ∈ Set.range P.path, 0 ≤ height (z - q))
    (outside : height (c - q) < 0)
    (outward : 0 < inner ℝ (P.vertex (Fin.last (n + 1)) - q)
      (c - P.vertex (Fin.last (n + 1)))) :
    ∀ᶠ z in 𝓝 (P.vertex 0), z ∈ P.threeSegmentClosure q c ↔
      z - P.vertex 0 ∈ nonnegativeRay (P.edge 0) ∪ nonnegativeRay (q - P.vertex 0) := by
  let a := P.vertex 0
  let b := P.vertex (Fin.last (n + 1))
  have away_terminal : a ∉ segment ℝ b c := by
    intro member
    have same := terminal_segment_inter_radial_disk q b c outward
    have equal := Set.mem_singleton_iff.mp (same.subset ⟨member, progress.le⟩)
    exact (ne_of_apply_ne (dist q) progress.ne) equal
  have away_middle : a ∉ segment ℝ c q := by
    intro member
    rw [segment_symm ℝ c q] at member
    have same := source_segments_inter height q a c (supported a (P.vertex_mem_path_range 0))
      outside
    have equal := Set.mem_singleton_iff.mp (same.subset ⟨right_mem_segment ℝ q a, member⟩)
    exact (dist_pos.mp initial) equal.symm
  have local_bank := P.eventually_mem_radial_path_iff_initial_ray q radial genuine
  have local_link := eventually_mem_segment_iff_nonnegativeRay a q
  filter_upwards [local_bank, local_link,
    (compact_segment b c).isClosed.isOpen_compl.mem_nhds away_terminal,
    (compact_segment c q).isClosed.isOpen_compl.mem_nhds away_middle] with z bank link hb hc
  change z ∉ segment ℝ b c at hb
  change z ∉ segment ℝ c q at hc
  change (z ∈ Set.range P.path ∨ (z ∈ segment ℝ b c ∨ z ∈ segment ℝ c q) ∨
    z ∈ segment ℝ q a) ↔
    z - a ∈ nonnegativeRay (P.edge 0) ∪ nonnegativeRay (q - a)
  simp only [Set.mem_union, hb, hc, false_or, bank, segment_symm ℝ q a, link]
  rfl

/-- The closure has its backward bank ray and ray toward the closing point at the last trim. -/
theorem eventually_mem_radialClosure_iff_terminal_rays
    (radial : P.RadialFrom q 0) (genuine : ∀ i, P.edge i ≠ 0)
    (progress : dist q (P.vertex 0) < dist q (P.vertex (Fin.last (n + 1))))
    (height : Plane →ₗ[ℝ] ℝ) (supported : ∀ z ∈ Set.range P.path, 0 ≤ height (z - q))
    (outside : height (c - q) < 0) :
    let b := P.vertex (Fin.last (n + 1))
    ∀ᶠ z in 𝓝 b, z ∈ P.threeSegmentClosure q c ↔
      z - b ∈ nonnegativeRay (-P.edge (Fin.last n)) ∪ nonnegativeRay (c - b) := by
  let a := P.vertex 0
  let b := P.vertex (Fin.last (n + 1))
  have away_initial : b ∉ segment ℝ q a := fun member =>
    progress.not_ge (dist_initial_segment_le q a member)
  have away_middle : b ∉ segment ℝ c q := by
    intro member
    rw [segment_symm ℝ c q] at member
    have same := source_segments_inter height q b c
      (supported b (P.vertex_mem_path_range (Fin.last (n + 1)))) outside
    have equal := Set.mem_singleton_iff.mp (same.subset ⟨right_mem_segment ℝ q b, member⟩)
    exact (dist_pos.mp (dist_nonneg.trans_lt progress)) equal.symm
  have local_bank := P.eventually_mem_radial_path_iff_terminal_ray q radial genuine
  have local_link := eventually_mem_segment_iff_nonnegativeRay b c
  change ∀ᶠ z in 𝓝 b, _
  filter_upwards [local_bank, local_link,
    (compact_segment q a).isClosed.isOpen_compl.mem_nhds away_initial,
    (compact_segment c q).isClosed.isOpen_compl.mem_nhds away_middle] with z bank link ha hc
  change z ∉ segment ℝ q a at ha
  change z ∉ segment ℝ c q at hc
  change (z ∈ Set.range P.path ∨ (z ∈ segment ℝ b c ∨ z ∈ segment ℝ c q) ∨
    z ∈ segment ℝ q a) ↔
    z - b ∈ nonnegativeRay (-P.edge (Fin.last n)) ∪ nonnegativeRay (c - b)
  simp only [Set.mem_union, ha, hc, or_false, bank, link]
  rfl

end Unfoldings.PolygonalChain
