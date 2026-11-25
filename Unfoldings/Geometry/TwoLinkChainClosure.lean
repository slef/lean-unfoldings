module

public import Unfoldings.Geometry.ChainLinearGraph
public import Unfoldings.Topology.PathJordanArc
public import Schoenflies.Polygonal

/-! Two supporting lines close a chain in an acute heading cone to a Jordan curve. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n)
  (h k : Plane →L[ℝ] ℝ)

private theorem linear_endpoint_lt (nonempty : 0 < n)
    (progress : ∀ i, 0 < h (P.edge i)) :
    h (P.vertex 0) < h (P.vertex (Fin.last n)) := by
  let first : Fin n := ⟨0, nonempty⟩
  have step := progress first
  rw [edge, map_sub, sub_pos] at step
  have monotone := (P.monotone_linear_vertices_iff h.toLinearMap).mpr
    (fun i => (progress i).le)
  exact step.trans_le (monotone (Fin.le_last first.succ))

/-- A strictly increasing linear coordinate makes the geometric chain an arc
with the original endpoints. -/
theorem isArcBetween_of_linear_progress (nonempty : 0 < n)
    (progress : ∀ i, 0 < h (P.edge i)) :
    Schoenflies.IsArcBetween (Set.range P.path) (P.vertex 0) (P.vertex (Fin.last n)) := by
  let a := h (P.vertex 0)
  let b := h (P.vertex (Fin.last n))
  have ordered : a < b := P.linear_endpoint_lt h nonempty progress
  have flat (i : Fin n) (zero : h (P.edge i) = 0) : P.edge i = 0 :=
    ((progress i).ne' zero).elim
  let coord := P.linearGraphHomeomorph h (fun i => (progress i).le) flat nonempty
  let time (t : unitInterval) : Set.Icc a b := ⟨AffineMap.lineMap a b t.val, by
    rw [← segment_eq_Icc ordered.le]
    exact lineMap_mem_segment ℝ _ _ t.property⟩
  have time_cont : Continuous time :=
    (AffineMap.lineMap_continuous.comp continuous_subtype_val).subtype_mk _
  have time_inj : Function.Injective time := fun _ _ eq =>
    Subtype.ext ((AffineMap.lineMap_injective ℝ ordered.ne) (congrArg Subtype.val eq))
  have time_surj : Function.Surjective time := by
    intro x
    have member := (segment_eq_Icc ordered.le).symm.subset x.property
    obtain ⟨t, ht, equal⟩ := (segment_eq_image_lineMap ℝ a b).subset member
    exact ⟨⟨t, ht⟩, Subtype.ext equal⟩
  let trace : Path (P.vertex 0) (P.vertex (Fin.last n)) := {
    toFun t := (coord.symm (time t)).val
    continuous_toFun := continuous_subtype_val.comp (coord.symm.continuous.comp time_cont)
    source' := by
      have h0 : time 0 = coord ⟨P.vertex 0, ⟨0, P.path.source⟩⟩ := by
        apply Subtype.ext
        change AffineMap.lineMap a b 0 = a
        exact AffineMap.lineMap_apply_zero a b
      rw [h0, coord.symm_apply_apply]
    target' := by
      have h1 : time 1 = coord ⟨P.vertex (Fin.last n), ⟨1, P.path.target⟩⟩ := by
        apply Subtype.ext
        change AffineMap.lineMap a b 1 = b
        exact AffineMap.lineMap_apply_one a b
      rw [h1, coord.symm_apply_apply] }
  have range_eq : Set.range trace = Set.range P.path := by
    apply Set.Subset.antisymm
    · rintro _ ⟨t, rfl⟩
      exact (coord.symm (time t)).property
    · intro z member
      obtain ⟨t, at_z⟩ := time_surj (coord ⟨z, member⟩)
      refine ⟨t, ?_⟩
      change (coord.symm (time t)).val = z
      rw [at_z, coord.symm_apply_apply]
  rw [← range_eq]
  exact PlanarTopology.isArcBetween_of_injective_path trace
    (Subtype.val_injective.comp (coord.symm.injective.comp time_inj))

/-- For the lower closure in a bisector chart the controls are `x + y` and
`x - y`. Interchanging them gives the upper closure. -/
theorem twoLinkClosure_jordan (nonempty : 0 < n)
    (first : ∀ i, 0 < h (P.edge i)) (second : ∀ i, 0 < k (P.edge i))
    (joint : Function.Injective fun z => (h z, k z))
    (c : Plane) (initial : h c = h (P.vertex 0)) (terminal : k c = k (P.vertex (Fin.last n))) :
    Schoenflies.IsJordanCurve (Set.range P.path ∪
      (segment ℝ (P.vertex (Fin.last n)) c ∪ segment ℝ c (P.vertex 0))) := by
  let a := P.vertex 0
  let b := P.vertex (Fin.last n)
  have h_lt : h a < h b := P.linear_endpoint_lt h nonempty first
  have k_lt : k a < k b := P.linear_endpoint_lt k nonempty second
  have a_ne : c ≠ a := fun eq => k_lt.ne ((congrArg k eq).symm.trans terminal)
  have b_ne : b ≠ c := fun eq => h_lt.ne (initial.symm.trans (congrArg h eq).symm)
  have h_flat (i : Fin n) (zero : h (P.edge i) = 0) : P.edge i = 0 :=
    ((first i).ne' zero).elim
  have k_flat (i : Fin n) (zero : k (P.edge i) = 0) : P.edge i = 0 :=
    ((second i).ne' zero).elim
  have at_first {z : Plane} (member : z ∈ segment ℝ c a) : h z = h a := by
    obtain ⟨t, _, loc⟩ := (segment_eq_image_lineMap ℝ _ _).subset member
    rw [← loc]
    change h.toLinearMap.toAffineMap (AffineMap.lineMap c a t) = _
    rw [h.toLinearMap.toAffineMap.apply_lineMap]
    change AffineMap.lineMap (h c) (h a) t = h a
    rw [initial, AffineMap.lineMap_same]
    rfl
  have at_last {z : Plane} (member : z ∈ segment ℝ b c) : k z = k b := by
    obtain ⟨t, _, loc⟩ := (segment_eq_image_lineMap ℝ _ _).subset member
    rw [← loc]
    change k.toLinearMap.toAffineMap (AffineMap.lineMap b c t) = _
    rw [k.toLinearMap.toAffineMap.apply_lineMap]
    change AffineMap.lineMap (k b) (k c) t = k b
    rw [terminal, AffineMap.lineMap_same]
    rfl
  have closing := (Schoenflies.isArcBetween_segment b_ne).concatenate
    (Schoenflies.isArcBetween_segment a_ne) (fun z last first =>
      joint (Prod.ext ((at_first first).trans initial.symm) ((at_last last).trans terminal.symm)))
  have chain := P.isArcBetween_of_linear_progress h nonempty first
  apply Schoenflies.IsJordanCurve.of_two_arcs chain closing
  intro z hz closed
  rcases closed with last | first_mem
  · exact Or.inr (P.path_linear_injOn k (fun i => (second i).le) k_flat nonempty
      hz ⟨1, P.path.target⟩ (at_last last))
  · exact Or.inl (P.path_linear_injOn h (fun i => (first i).le) h_flat nonempty
      hz ⟨0, P.path.source⟩ (at_first first_mem))

end Unfoldings.PolygonalChain
