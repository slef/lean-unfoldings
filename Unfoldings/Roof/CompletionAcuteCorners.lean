module

public import Unfoldings.Roof.CompletionRegularCorners
public import Unfoldings.Cap.AcuteJordanBankBudget
public import Unfoldings.Geometry.AcuteChainEndpointRays

/-! Regular trimmed acute closures give the exact corner and crease budgets in the completion. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

open Filter Topology Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane} {I : Type u}
  {extra : I → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra)

open Classical in
/-- A two-link closure trimmed into the old bank edges has exactly three
corners to charge by the original single-face corner estimate. -/
theorem regular_acute_closing_corners {n : ℕ} (P : PolygonalChain Plane (n + 1)) (c : Plane)
    (h k : Plane →L[ℝ] ℝ) (first : ∀ i, 0 < h (P.edge i)) (last : ∀ i, 0 < k (P.edge i))
    (initial : h c ≤ h (P.vertex 0)) (terminal : k (P.vertex (Fin.last (n + 1))) ≤ k c)
    (contained : P.twoLinkClosure c ⊆ region)
    (bank_edges : ∀ f, Disjoint (interior (E.mesh.projectedTriangle f).carrier) (Set.range P.path))
    (trim_avoids : ∀ (f : E.mesh.Index) (i : Fin 3),
      P.vertex 0 ≠ (E.mesh.projectedTriangle f).vertex i ∧
        P.vertex (Fin.last (n + 1)) ≠ (E.mesh.projectedTriangle f).vertex i)
    (off_edges : ∀ f i, c ∉ (E.mesh.projectedTriangle f).edge i) :
    ∀ p ∈ P.twoClosingCorners c, E.RegularClosingCorner (P.twoLinkClosure c) p := by
  let a := P.vertex 0
  let b := P.vertex (Fin.last (n + 1))
  let J := P.twoLinkClosure c
  have in_mesh {p : Plane} (point : p ∈ J) : ∃ f, p ∈ (E.mesh.projectedTriangle f).carrier :=
    Set.mem_iUnion.mp (E.mesh.cover.subset (interior_subset (E.covers (Or.inr (contained point)))))
  have in_skeleton {p : Plane} (point : p ∈ Set.range P.path) :
      ∃ f, p ∈ (E.mesh.projectedTriangle f).carrier ∧
        p ∉ interior (E.mesh.projectedTriangle f).carrier := by
    obtain ⟨f, member⟩ := in_mesh (Or.inl point)
    exact ⟨f, member, fun inside => Set.disjoint_left.mp (bank_edges f) inside point⟩
  have small_t : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds zero_lt_one)
  have near_forward : ∀ᶠ t : ℝ in 𝓝[>] 0, a + t • P.edge 0 ∈ Set.range P.path := by
    filter_upwards [self_mem_nhdsWithin, small_t] with t t_pos t_small
    let s : unitInterval := ⟨t, (show 0 < t from t_pos).le, t_small.le⟩
    have same : P.point 0 s = a + t • P.edge 0 := by
      rw [PolygonalChain.point, AffineMap.lineMap_apply_module', add_comm]
      rfl
    rw [← same]
    exact P.point_mem_path_range _ _
  have near_backward : ∀ᶠ t : ℝ in 𝓝[>] 0, b + t • (-P.edge (Fin.last n)) ∈ Set.range P.path := by
    filter_upwards [self_mem_nhdsWithin, small_t] with t t_positive t_small
    have t_pos : 0 < t := t_positive
    let s : unitInterval := ⟨1 - t, by constructor <;> linarith⟩
    have same : P.point (Fin.last n) s = b + t • (-P.edge (Fin.last n)) := by
      rw [PolygonalChain.point, PolygonalChain.edge, AffineMap.lineMap_apply_module', Fin.succ_last]
      dsimp only [s, b]
      module
    rw [← same]
    exact P.point_mem_path_range _ _
  intro p member
  simp only [PolygonalChain.twoClosingCorners, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with at_first | at_last | at_apex
  · subst p
    apply E.regularClosingCorner_of_locally_on_old_skeleton J a (P.edge 0) (c - a)
    · rintro f ⟨i, eq⟩
      exact (trim_avoids f i).1 eq.symm
    · exact near_forward.mono (fun _ member => in_skeleton member)
    · exact (P.eventually_mem_twoLinkClosure_iff_initial_rays c k last terminal).mono
        (fun _ same => same.mp)
  · subst p
    apply E.regularClosingCorner_of_locally_on_old_skeleton J b (-P.edge (Fin.last n)) (c - b)
    · rintro f ⟨i, eq⟩
      exact (trim_avoids f i).2 eq.symm
    · exact near_backward.mono (fun _ member => in_skeleton member)
    · exact (P.eventually_mem_twoLinkClosure_iff_terminal_rays c h first initial).mono
        (fun _ same => same.mp)
  · subst p
    exact E.regularClosingCorner_of_off_old_edges J c
      (in_mesh (Or.inr (Or.inl (right_mem_segment ℝ b c)))) off_edges

end Unfoldings.ConvexRoof.CompletionMesh
