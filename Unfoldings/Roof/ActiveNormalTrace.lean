module

public import Unfoldings.Convex.ActiveCell
public import Unfoldings.Geometry.ChainGraphLenses
public import Unfoldings.Roof.NormalRibbonCancellation

/-! Interpolate the actual active normals encountered by one horizontal roof link. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope

open PlanarTopology

/-- Consecutive normals at the same physical contact can be joined inside its
active polygon. For a strictly advancing normal chain this produces a continuous
graph, each point of which is active somewhere on the original horizontal link. -/
theorem exists_activeNormalGraph (E : SlopeEnvelope) (convex : Convex ℝ E.slopes)
    (dual_convex : ConvexOn ℝ Set.univ E.dual)
    {n : ℕ} (P : PolygonalChain Plane n) (nonempty : 0 < n)
    (monotone : ∀ i, 0 < (P.edge i) 0)
    (x : Fin n → Plane) (level : ℝ) (on_line : ∀ i, (x i) 1 = level)
    (before : ∀ i, E.Active (x i) (P.vertex i.castSucc))
    (after : ∀ i, E.Active (x i) (P.vertex i.succ)) :
    ∃ trace : ℝ → ℝ, Continuous trace ∧
      (∀ i, trace (P.vertex i 0) = P.vertex i 1) ∧
      graphPoint trace '' Set.Icc (P.vertex 0 0) (P.vertex (Fin.last n) 0) = Set.range P.path ∧
      ∀ p ∈ Set.Icc (P.vertex 0 0) (P.vertex (Fin.last n) 0),
        ∃ contact : Plane, contact 1 = level ∧ E.Active contact (graphPoint trace p) := by
  obtain ⟨trace, continuous, interpolates, graph⟩ :=
    P.exists_continuous_graph_of_horizontal nonempty monotone
  refine ⟨trace, continuous, interpolates, graph, fun p near => ?_⟩
  have member : graphPoint trace p ∈ Set.range P.path := graph ▸ ⟨p, near, rfl⟩
  rw [P.path_range_eq_segments] at member
  rcases member with first | rest
  · have eq : graphPoint trace p = P.vertex 0 := first
    let i : Fin n := ⟨0, nonempty⟩
    exact ⟨x i, on_line i, eq.symm ▸ before i⟩
  · obtain ⟨i, segment⟩ := Set.mem_iUnion.mp rest
    exact ⟨x i, on_line i,
      (E.convex_active_cell convex dual_convex (x i)).segment_subset (before i) (after i) segment⟩

end Unfoldings.SlopeEnvelope

namespace Unfoldings

open PlanarTopology

private theorem graph_vertical_between_mem {C : Set Plane} (convex : Convex ℝ C)
    {trace chord : ℝ → ℝ} {a b : ℝ}
    (trace_in : ∀ p ∈ Set.Ioc a b, graphPoint trace p ∈ C)
    (chord_in : ∀ p ∈ Set.Ioc a b, graphPoint chord p ∈ C)
    {z : ℝ × ℝ} (inside : z ∈ graphRibbon trace chord a b) :
    z ∈ Cap.planeCartesian '' C := by
  let x := z.1
  let t := (z.2 - trace x) / (chord x - trace x)
  have denom : 0 < chord x - trace x := sub_pos.mpr (inside.2.1.trans_le inside.2.2)
  have t_mem : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr inside.2.1.le) denom.le,
      (div_le_one₀ denom).mpr (sub_le_sub_right inside.2.2 _)⟩
  let p := AffineMap.lineMap (graphPoint trace x) (graphPoint chord x) t
  have p_mem : p ∈ C :=
    (convex.segment_subset (trace_in x inside.1) (chord_in x inside.1))
      ((segment_eq_image_lineMap ℝ _ _).superset ⟨t, t_mem, rfl⟩)
  refine ⟨p, p_mem, ?_⟩
  rw [Cap.planeCartesian_apply]
  unfold p
  rw [AffineMap.lineMap_apply_module']
  apply Prod.ext
  · change t * (x - x) + x = x
    ring
  · change t * (chord x - trace x) + trace x = z.2
    rw [div_mul_cancel₀ _ denom.ne']
    ring

/-- The ribbon joining a normal trace to its chord stays within the convex selector. -/
theorem graphRibbons_subset_convex {C : Set Plane} (convex : Convex ℝ C)
    {trace chord : ℝ → ℝ} {a b : ℝ}
    (trace_in : ∀ p ∈ Set.Ioc a b, graphPoint trace p ∈ C)
    (chord_in : ∀ p ∈ Set.Ioc a b, graphPoint chord p ∈ C) :
    graphRibbon trace chord a b ∪ graphRibbon chord trace a b ⊆ Cap.planeCartesian '' C :=
  fun _ hz => hz.elim (graph_vertical_between_mem convex trace_in chord_in)
    (graph_vertical_between_mem convex chord_in trace_in)

end Unfoldings
