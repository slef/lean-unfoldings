module

public import Unfoldings.Geometry.RadialChain
public import Unfoldings.Geometry.ChainPaths
public import Unfoldings.Geometry.BankRadialOrder
public import Unfoldings.Topology.IntervalArc

/-! Radially monotone polygonal carriers are interval arcs after removing flat repetitions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n) (source : E) (radial : P.RadialFrom source 0)

include radial in
theorem path_radius_bounds {x : E} (member : x ∈ Set.range P.path) :
    dist source (P.vertex 0) ≤ dist source x ∧
      dist source x ≤ dist source (P.vertex (Fin.last n)) := by
  have vertices := PolygonalChain.RadialFrom.dist_vertices_le P radial
  have cover := P.path_range.subset member
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at cover
  rcases cover with root | ⟨i, t, rfl⟩
  · rw [Set.mem_singleton_iff.mp root]
    exact ⟨le_rfl, vertices 0 (Fin.last n) le_rfl (Fin.zero_le _)⟩
  · have first := radial i (Nat.zero_le _) (show (0 : unitInterval) ≤ t from t.property.1)
    have last := radial i (Nat.zero_le _) (show t ≤ (1 : unitInterval) from t.property.2)
    change dist source (P.point i 0) ≤ dist source (P.point i t) at first
    change dist source (P.point i t) ≤ dist source (P.point i 1) at last
    rw [P.point_zero] at first
    rw [P.point_one] at last
    exact ⟨(vertices 0 i.castSucc le_rfl (Fin.zero_le _)).trans first,
      last.trans (vertices i.succ (Fin.last n) (Fin.zero_le _) (Fin.le_last _))⟩

include radial in
theorem path_radius_range : Set.range (fun t => dist source (P.path t)) =
    Set.Icc (dist source (P.vertex 0)) (dist source (P.vertex (Fin.last n))) := by
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    exact P.path_radius_bounds source radial (Set.mem_range_self t)
  · have connected := isPreconnected_range
      (f := fun t => dist source (P.path t)) (continuous_const.dist P.path.continuous)
    apply connected.Icc_subset
    · exact ⟨0, congrArg (dist source) P.path.source⟩
    · exact ⟨1, congrArg (dist source) P.path.target⟩

include radial in
theorem path_radius_injOn (positive : 0 < n) :
    Set.InjOn (dist source) (Set.range P.path) := by
  rintro x ⟨s, rfl⟩ y ⟨t, rfl⟩ equal
  obtain ⟨i, a, first⟩ := P.path_point_covered positive s
  obtain ⟨j, b, last⟩ := P.path_point_covered positive t
  rw [first, last] at equal ⊢
  rcases before_total i j a b with before | before
  · exact PolygonalChain.RadialFrom.point_eq_of_dist_eq P radial i j a b
      (Nat.zero_le _) before equal
  · exact (PolygonalChain.RadialFrom.point_eq_of_dist_eq P radial j i b a
      (Nat.zero_le _) before equal.symm).symm

/-- The controlling radius is the true radius of every point of every original edge. -/
def radialGraphHomeomorph (positive : 0 < n) : Set.range P.path ≃ₜ
    Set.Icc (dist source (P.vertex 0)) (dist source (P.vertex (Fin.last n))) := by
  let coordinate : Set.range P.path →
      Set.Icc (dist source (P.vertex 0)) (dist source (P.vertex (Fin.last n))) :=
    fun x => ⟨dist source x.val, P.path_radius_bounds source radial x.property⟩
  have injective : Function.Injective coordinate := by
    intro x y equal
    exact Subtype.ext (P.path_radius_injOn source radial positive x.property y.property
      (congrArg Subtype.val equal))
  have surjective : Function.Surjective coordinate := by
    intro y
    obtain ⟨t, equal⟩ := (P.path_radius_range source radial).symm.subset y.property
    exact ⟨⟨P.path t, Set.mem_range_self t⟩, Subtype.ext equal⟩
  let : CompactSpace (Set.range P.path) :=
    isCompact_iff_compactSpace.mp (isCompact_range P.path.continuous)
  let equivalence := Equiv.ofBijective coordinate ⟨injective, surjective⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := equivalence)
    ((continuous_const.dist continuous_subtype_val).subtype_mk _)

include radial in
/-- Flat edges may repeat parameters; the whole geometric carrier has a simple parametrization. -/
theorem exists_injective_radial_path
    (progress : dist source (P.vertex 0) < dist source (P.vertex (Fin.last n))) :
    ∃ Q : Path (P.vertex 0) (P.vertex (Fin.last n)),
      Function.Injective Q ∧ Set.range Q = Set.range P.path := by
  have positive : 0 < n := by
    by_contra zero
    have same : n = 0 := by omega
    subst n
    exact (lt_irrefl _ progress)
  let graph := P.radialGraphHomeomorph source radial positive
  let first : Set.range P.path := ⟨P.vertex 0, 0, P.path.source⟩
  let last : Set.range P.path := ⟨P.vertex (Fin.last n), 1, P.path.target⟩
  have start_eq : graph.symm ⟨dist source (P.vertex 0), le_rfl, progress.le⟩ = first := by
    apply graph.injective
    rw [graph.apply_symm_apply]
    exact Subtype.ext rfl
  have end_eq : graph.symm ⟨dist source (P.vertex (Fin.last n)), progress.le, le_rfl⟩ = last := by
    apply graph.injective
    rw [graph.apply_symm_apply]
    exact Subtype.ext rfl
  let arc := intervalHomeomorphPath progress.le graph.symm
  refine ⟨arc.cast (congrArg Subtype.val start_eq).symm (congrArg Subtype.val end_eq).symm, ?_, ?_⟩
  · exact intervalHomeomorphPath_injective progress graph.symm
  · exact intervalHomeomorphPath_range progress.le graph.symm

end Unfoldings.PolygonalChain
