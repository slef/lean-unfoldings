module

public import Unfoldings.Geometry.PolygonalBankTailGerm
public import Unfoldings.Geometry.RadialGraphArc

/-! Exact local incoming and outgoing rays of genuine source-radial polygonal chains. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- Genuine edges make source radii strictly increase, including at a zero initial derivative. -/
theorem vertex_radius_strictMono_of_radial (P : PolygonalChain E n) (source : E)
    (radial : P.RadialFrom source 0) (genuine : ∀ i, P.edge i ≠ 0) :
    StrictMono (fun i => dist source (P.vertex i)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have initial := (monotone_dist_lineMap_iff source (P.vertex i.castSucc)
    (P.vertex i.succ)).mp (radial i (Nat.zero_le _))
  have different : P.vertex i.castSucc ≠ P.vertex i.succ :=
    fun same => genuine i (by simp only [edge, same, sub_self])
  simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
    dist_lineMap_lt_of_inner_nonneg source _ _ initial different
      (show (0 : ℝ) ≤ 0 from le_rfl) (show (0 : ℝ) < 1 by norm_num)

/-- Radial order prevents any original vertex from occurring inside an original bank edge. -/
theorem vertex_not_mem_openSegment_of_radial (P : PolygonalChain E n) (source : E)
    (radial : P.RadialFrom source 0) (genuine : ∀ i, P.edge i ≠ 0)
    (k : Fin (n + 1)) (i : Fin n) :
    P.vertex k ∉ openSegment ℝ (P.vertex i.castSucc) (P.vertex i.succ) := by
  intro member
  rw [openSegment_eq_image_lineMap] at member
  obtain ⟨t, bounds, equal⟩ := member
  have initial := (monotone_dist_lineMap_iff source (P.vertex i.castSucc)
    (P.vertex i.succ)).mp (radial i (Nat.zero_le _))
  have different : P.vertex i.castSucc ≠ P.vertex i.succ :=
    fun same => genuine i (by simp only [edge, same, sub_self])
  have first := dist_lineMap_lt_of_inner_nonneg source _ _ initial different
    (show (0 : ℝ) ≤ 0 from le_rfl) bounds.1
  have last := dist_lineMap_lt_of_inner_nonneg source _ _ initial different bounds.1.le bounds.2
  rw [AffineMap.lineMap_apply_zero, equal] at first
  rw [AffineMap.lineMap_apply_one, equal] at last
  have monotone := (P.vertex_radius_strictMono_of_radial source radial genuine).monotone
  by_cases before : k ≤ i.castSucc
  · exact (not_lt_of_ge (monotone before)) first
  · have after : i.succ ≤ k := by
      have ordered := lt_of_not_ge before
      change i.val + 1 ≤ k.val
      change i.val < k.val at ordered
      omega
    exact (not_lt_of_ge (monotone after)) last

/-- At an internal simple-chain vertex the whole local path is its two actual incident rays. -/
theorem eventually_mem_path_iff_internal_rays (P : PolygonalChain E (n + 1))
    (injective : Function.Injective P.vertex) (k : Fin n)
    (not_open : ∀ i : Fin (n + 1), P.vertex k.succ.castSucc ∉
      openSegment ℝ (P.vertex i.castSucc) (P.vertex i.succ)) :
    ∀ᶠ z in 𝓝 (P.vertex k.succ.castSucc), z ∈ Set.range P.path ↔
      z - P.vertex k.succ.castSucc ∈
        nonnegativeRay (P.vertex k.castSucc.castSucc - P.vertex k.succ.castSucc) ∪
        nonnegativeRay (P.vertex k.succ.succ - P.vertex k.succ.castSucc) := by
  classical
  have not_first : P.vertex k.succ.castSucc ≠ P.vertex 0 := by
    intro same
    have values := congrArg Fin.val (injective same)
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_zero] at values
    omega
  have no_first : ∀ᶠ z in 𝓝 (P.vertex k.succ.castSucc), z ∉ ({P.vertex 0} : Set E) :=
    isClosed_singleton.isOpen_compl.mem_nhds not_first
  have near := eventually_mem_segment_family_iff_incident_rays
    (fun i : Fin (n + 1) => P.vertex i.castSucc) (fun i => P.vertex i.succ)
    (P.vertex k.succ.castSucc) not_open
  have at_first (i : Fin (n + 1)) :
      P.vertex k.succ.castSucc = P.vertex i.castSucc ↔ i = k.succ := by
    constructor
    · intro same
      apply Fin.ext
      exact (congrArg Fin.val (injective same)).symm
    · rintro rfl
      rfl
  have at_last (i : Fin (n + 1)) :
      P.vertex k.succ.castSucc = P.vertex i.succ ↔ i = k.castSucc := by
    constructor
    · intro same
      apply Fin.ext
      have values := congrArg Fin.val (injective same)
      simp only [Fin.val_castSucc, Fin.val_succ] at values
      change i.val = k.val
      omega
    · rintro rfl
      exact congrArg P.vertex (Fin.ext rfl)
  have model : segmentIncidentRays (fun i : Fin (n + 1) => P.vertex i.castSucc)
      (fun i => P.vertex i.succ) (P.vertex k.succ.castSucc) =
        nonnegativeRay (P.vertex k.castSucc.castSucc - P.vertex k.succ.castSucc) ∪
        nonnegativeRay (P.vertex k.succ.succ - P.vertex k.succ.castSucc) := by
    simp only [segmentIncidentRays]
    simp_rw [at_first, at_last]
    simp [Set.iUnion_union_distrib, Set.iUnion_ite, Set.union_comm]
  filter_upwards [no_first, near] with z outside local_model
  rw [P.path_range_eq_segments]
  simpa only [Set.mem_union, outside, false_or, model] using local_model

/-- A disjoint closed rest of the curve cannot change either original hinge direction. -/
theorem eventually_mem_path_union_iff_internal_rays (P : PolygonalChain E (n + 1))
    (source : E) (radial : P.RadialFrom source 0) (genuine : ∀ i, P.edge i ≠ 0)
    (k : Fin n) {rest : Set E} (closed : IsClosed rest)
    (outside : P.vertex k.succ.castSucc ∉ rest) :
    ∀ᶠ z in 𝓝 (P.vertex k.succ.castSucc), z ∈ Set.range P.path ∪ rest ↔
      z - P.vertex k.succ.castSucc ∈
        nonnegativeRay (P.vertex k.castSucc.castSucc - P.vertex k.succ.castSucc) ∪
        nonnegativeRay (P.vertex k.succ.succ - P.vertex k.succ.castSucc) := by
  have injective : Function.Injective P.vertex := fun _ _ same =>
    (P.vertex_radius_strictMono_of_radial source radial genuine).injective
      (congrArg (dist source) same)
  have near := P.eventually_mem_path_iff_internal_rays injective k
    (P.vertex_not_mem_openSegment_of_radial source radial genuine k.succ.castSucc)
  filter_upwards [near, closed.isOpen_compl.mem_nhds outside] with z model avoids
  change z ∉ rest at avoids
  simpa only [Set.mem_union, avoids, or_false] using model

end Unfoldings.PolygonalChain
