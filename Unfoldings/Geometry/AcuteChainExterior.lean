module

public import Unfoldings.Geometry.AcuteChainClosure
public import Unfoldings.Topology.ClosedJordanDomain
public import Unfoldings.Geometry.SegmentVertices

/-! The closing disk is on the chosen side, as certified by rays escaping to infinity. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

open Filter Topology

variable {n : ℕ} (P : PolygonalChain Plane n) (c : Plane)
  (h k : Plane →L[ℝ] ℝ)
  (first : ∀ i, 0 < h (P.edge i)) (last : ∀ i, 0 < k (P.edge i))
  (initial : h c ≤ h (P.vertex 0)) (terminal : k (P.vertex (Fin.last n)) ≤ k c)

include first last initial terminal in
/-- The open vertical ray on the side opposite the two closing links avoids the whole curve. -/
theorem acute_exterior_ray_avoids (nonempty : 0 < n)
    {p v : Plane} (bank : p ∈ Set.range P.path)
    (not_first : p ≠ P.vertex 0) (not_last : p ≠ P.vertex (Fin.last n))
    (up : 0 < h v) (orthogonal : h v + k v = 0) {t : ℝ} (pos : 0 < t) :
    p + t • v ∉ P.twoLinkClosure c := by
  let horizontal := h + k
  have grows (i : Fin n) : 0 < horizontal (P.edge i) :=
    add_pos (first i) (last i)
  have h_lo : h (P.vertex 0) < h p := by
    have le := (P.path_linear_bounds h (fun i => (first i).le) bank).1
    apply le.lt_of_ne
    intro eq
    exact not_first (P.path_linear_injOn h (fun i => (first i).le)
      (fun i zero => ((first i).ne' zero).elim) nonempty bank ⟨0, P.path.source⟩ eq.symm)
  have k_hi : k p < k (P.vertex (Fin.last n)) := by
    have le := (P.path_linear_bounds k (fun i => (last i).le) bank).2
    apply le.lt_of_ne
    intro eq
    exact not_last (P.path_linear_injOn k (fun i => (last i).le)
      (fun i zero => ((last i).ne' zero).elim) nonempty bank ⟨1, P.path.target⟩ eq)
  have down : k v < 0 := by linarith only [up, orthogonal]
  rintro (on_bank | on_last | on_first)
  · have same : horizontal (p + t • v) = horizontal p := by
      rw [map_add, map_smul, smul_eq_mul]
      change horizontal p + t * (h v + k v) = horizontal p
      rw [orthogonal, mul_zero, add_zero]
    have eq := P.path_linear_injOn horizontal (fun i => (grows i).le)
      (fun i zero => ((grows i).ne' zero).elim) nonempty on_bank bank same
    have height_eq := congrArg h eq
    rw [map_add, map_smul, smul_eq_mul] at height_eq
    linarith only [height_eq, mul_pos pos up]
  · have height : k.toLinearMap.toAffineMap (p + t • v) ∈
        segment ℝ (k.toLinearMap.toAffineMap (P.vertex (Fin.last n))) (k.toLinearMap.toAffineMap c) :=
      (image_segment ℝ k.toLinearMap.toAffineMap _ _).subset (Set.mem_image_of_mem _ on_last)
    change k (p + t • v) ∈ segment ℝ (k (P.vertex (Fin.last n))) (k c) at height
    rw [segment_eq_Icc terminal] at height
    have low := height.1
    rw [map_add, map_smul, smul_eq_mul] at low
    linarith only [low, k_hi, mul_neg_of_pos_of_neg pos down]
  · have height : h.toLinearMap.toAffineMap (p + t • v) ∈
        segment ℝ (h.toLinearMap.toAffineMap c) (h.toLinearMap.toAffineMap (P.vertex 0)) :=
      (image_segment ℝ h.toLinearMap.toAffineMap _ _).subset (Set.mem_image_of_mem _ on_first)
    change h (p + t • v) ∈ segment ℝ (h c) (h (P.vertex 0)) at height
    rw [segment_eq_Icc initial] at height
    have high := height.2
    rw [map_add, map_smul, smul_eq_mul] at high
    linarith only [high, h_lo, mul_pos pos up]

include first last initial terminal in
/-- From any regular point of the bank a transverse ray on the opposite side
misses the filled disk, all the way to infinity. -/
theorem acute_exterior_ray_avoids_domain (nonempty : 0 < n)
    {p v : Plane} (bank : p ∈ Set.range P.path)
    (not_first : p ≠ P.vertex 0) (not_last : p ≠ P.vertex (Fin.last n))
    (up : 0 < h v) (orthogonal : h v + k v = 0) {t : ℝ} (pos : 0 < t) :
    p + t • v ∉ PlanarTopology.closedJordanDomain (P.twoLinkClosure c) := by
  let J := P.twoLinkClosure c
  have jordan : Schoenflies.IsJordanCurve J :=
    P.isJordanCurve_twoLinkClosure c h k first last initial terminal nonempty
  have avoids {s : ℝ} (hs : 0 < s) : p + s • v ∉ J :=
    P.acute_exterior_ray_avoids c h k first last initial terminal nonempty
      bank not_first not_last up orthogonal hs
  intro member
  have known : p + t • v ∈ Schoenflies.inside J := by
    by_contra absent
    apply avoids pos
    rw [← (Schoenflies.jordan_curve_theorem jordan).frontier_inside, frontier]
    exact ⟨member, fun point => absent (interior_subset point)⟩
  have nonzero : v ≠ 0 := by
    intro zero
    rw [zero, map_zero] at up
    exact (lt_irrefl _ up)
  have escape : ∀ s : ℝ, 0 ≤ s → p + t • v + s • v ∈ Jᶜ := by
    intro s hs
    change p + t • v + s • v ∉ J
    rw [add_assoc, ← add_smul]
    exact avoids (add_pos_of_pos_of_nonneg pos hs)
  exact PlanarTopology.not_isBounded_component_of_escape_ray nonzero escape known.2

variable (Q : PolygonalChain Plane (n + 1))

/-- Interior turns of a strictly progressing chain keep exactly their original
projected rays after the two closing links are attached. -/
theorem eventually_mem_twoLinkClosure_iff_internal_rays
    (first : ∀ i, 0 < h (Q.edge i)) (last : ∀ i, 0 < k (Q.edge i))
    (initial : h c ≤ h (Q.vertex 0)) (terminal : k (Q.vertex (Fin.last (n + 1))) ≤ k c)
    (i : Fin n) :
    ∀ᶠ z in 𝓝 (Q.vertex i.succ.castSucc), z ∈ Q.twoLinkClosure c ↔
      z - Q.vertex i.succ.castSucc ∈
        nonnegativeRay (Q.vertex i.castSucc.castSucc - Q.vertex i.succ.castSucc) ∪
        nonnegativeRay (Q.vertex i.succ.succ - Q.vertex i.succ.castSucc) := by
  let a := Q.vertex 0
  let b := Q.vertex (Fin.last (n + 1))
  let rest := segment ℝ b c ∪ segment ℝ c a
  have closed : IsClosed rest := (compact_segment b c).isClosed.union (compact_segment c a).isClosed
  have simple := (Q.strictMono_linear_vertices h first).injective
  have injective : Function.Injective Q.vertex := fun _ _ same => simple (congrArg h same)
  have outside : Q.vertex i.succ.castSucc ∉ rest := by
    intro member
    have contact := Q.twoLinkClosure_contacts c h k first last initial terminal (Nat.succ_pos n)
      ⟨Q.vertex_mem_path_range i.succ.castSucc, member⟩
    rcases contact with at_first | at_last
    · have eq := congrArg Fin.val (injective at_first)
      simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_zero] at eq
      omega
    · have eq := congrArg Fin.val (injective (Set.mem_singleton_iff.mp at_last))
      simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last] at eq
      have bound := i.isLt
      omega
  have near := Q.eventually_mem_path_iff_internal_rays injective i
    (Q.vertex_not_mem_openSegment_of_linear_progress h first i.succ.castSucc)
  filter_upwards [near, closed.isOpen_compl.mem_nhds outside] with z model away
  change z ∉ rest at away
  change (z ∈ Set.range Q.path ∨ z ∈ rest) ↔ _
  rcases model with ⟨forward, backward⟩
  exact ⟨fun member => forward (member.resolve_right away), fun hr => Or.inl (backward hr)⟩

end Unfoldings.PolygonalChain
