module

public import Unfoldings.Polyhedron.NonextremeCreaseCount
public import Unfoldings.Topology.CyclicLabels

/-!
# At most two actual incident planes at a nonextreme vertex

Every different cyclic plane label needs an entry across a genuine crease.
The proved two-crease bound therefore leaves at most two plane labels.
The resulting planes are actual incident face planes; they may coincide.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

theorem linkPlane_mate_eq_prev {v : C.Vertex Set.univ} {n : ℕ}
    (c : (C.linkSystem Set.univ v).Chain n)
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) :
    LinearMap.range (F.place (C.linkMate Set.univ v (c.point i)).val.1.1).linear =
      LinearMap.range (F.place (c.point ((finRotate (n + 1)).symm i)).val.1.1).linear := by
  refine Fin.cases ?_ (fun k => ?_) i
  · have start : C.linkMate Set.univ v c.first = C.linkTurn Set.univ v c.last := by
      rw [← closes, C.linkMate_involutive]
    have planes := congrArg (fun p : C.LinkGerm Set.univ v =>
      LinearMap.range (F.place p.val.1.1).linear) start
    rw [finRotate_symm_zero]
    exact planes
  · have planes := congrArg (fun p : C.LinkGerm Set.univ v =>
      LinearMap.range (F.place p.val.1.1).linear) (c.mate_succ k)
    rw [finRotate_symm_succ]
    exact planes

end Unfoldings.SpatialFolding

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem nonextreme_link_plane_count_le_two (v : C.Vertex Set.univ)
    (not_extreme : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∉ F.vertexHull.extremePoints ℝ)
    {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first) :
    (Finset.univ.image
      (fun i => LinearMap.range (F.place (c.point i).val.1.1).linear)).card ≤ 2 := by
  classical
  let label (i : Fin (n + 1)) := LinearMap.range (F.place (c.point i).val.1.1).linear
  have count := P.nonextreme_crease_count_le_two v not_extreme c closes
  rw [Fintype.card_subtype] at count
  have filters : Finset.univ.filter (fun i : Fin (n + 1) =>
      LinearMap.range (F.place (c.point i).val.1.1).linear ≠
        LinearMap.range (F.place (C.linkMate Set.univ v (c.point i)).val.1.1).linear) =
      Finset.univ.filter (fun i => label ((finRotate (n + 1)).symm i) ≠ label i) := by
    apply Finset.filter_congr
    intro i _
    rw [F.linkPlane_mate_eq_prev c closes i]
    exact ne_comm
  rw [filters] at count
  by_cases nonconstant : ∃ i j, label i ≠ label j
  · exact (cyclic_label_card_le_changes label nonconstant).trans count
  · have same (i) : label i = label 0 := by
      by_contra different
      exact nonconstant ⟨i, 0, different⟩
    have included : Finset.univ.image label ⊆ {label 0} := by
      intro U hU
      obtain ⟨i, _member, rfl⟩ := Finset.mem_image.mp hU
      exact Finset.mem_singleton.mpr (same i)
    exact (Finset.card_le_card included).trans (by simp)

theorem exists_two_incident_planes (v : C.Vertex Set.univ)
    (not_extreme : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∉ F.vertexHull.extremePoints ℝ) :
    ∃ a b : C.CornerAt Set.univ v, ∀ c : C.CornerAt Set.univ v,
      LinearMap.range (F.place c.val.1).linear = LinearMap.range (F.place a.val.1).linear ∨
        LinearMap.range (F.place c.val.1).linear = LinearMap.range (F.place b.val.1).linear := by
  classical
  obtain ⟨n, c, closes, covers⟩ := P.exists_cyclic_link v
  let label (i : Fin (n + 1)) := LinearMap.range (F.place (c.point i).val.1.1).linear
  have nonempty : (Finset.univ.image label).Nonempty :=
    Finset.univ_nonempty.image label
  obtain ⟨U, hU, V, hV, cover⟩ := exists_pair_mem_cover_of_card_le_two
    (Finset.univ.image label) nonempty (P.nonextreme_link_plane_count_le_two v not_extreme c closes)
  obtain ⟨i, _hi, at_i⟩ := Finset.mem_image.mp hU
  obtain ⟨j, _hj, at_j⟩ := Finset.mem_image.mp hV
  refine ⟨C.linkCornerEquiv Set.univ v c covers i, C.linkCornerEquiv Set.univ v c covers j, ?_⟩
  intro a
  obtain ⟨k, rfl⟩ := (C.linkCornerEquiv Set.univ v c covers).surjective a
  have alternatives := cover (label k) (Finset.mem_image_of_mem label (Finset.mem_univ k))
  rw [← at_i, ← at_j] at alternatives
  exact alternatives

end Unfoldings.SpatialFolding.ConvexBoundary
