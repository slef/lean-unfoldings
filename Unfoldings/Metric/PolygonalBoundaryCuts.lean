module

public import Unfoldings.Metric.PolygonalCutInterior

/-! Boundary cuts preserve convex-region coincidences and the full intrinsic metric. -/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace Unfoldings.MetricGluing

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite I]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i)) (cuts : Set E) {s : Set E}

/-- A cut confined to the boundary of a convex region cannot split one of its physical points.
All cells must be full dimensional; point-only redundant cells would give a false statement. -/
theorem cut_of_eq_of_boundary_cuts (convex : ∀ i, Convex ℝ (cells i))
    (full : ∀ i, (interior (cells i)).Nonempty) (cover : s = ⋃ i, cells i)
    (convex_s : Convex ℝ s) (cut_closed : IsClosed cuts)
    (outside : Disjoint (interior s) cuts)
    {i j : I} (x : cells i) (y : cells j) (same : x.val = y.val) :
    of (fun i => cells i) (cutSeams cells closed cuts).relation i x =
      of (fun i => cells i) (cutSeams cells closed cuts).relation j y := by
  let S := cutSeams cells closed cuts
  have regular (k : I) (z : cells k) : z.val ∈ closure (interior (cells k)) := by
    rw [(convex k).closure_interior_eq_closure_of_nonempty_interior (full k),
      (closed k).closure_eq]
    exact z.property
  have interior_included (k : I) : interior (cells k) ⊆ interior s :=
    interior_mono (cell_subset_of_cover cells cover k)
  have uncut {z : E} (inside : z ∈ interior s) : z ∉ cuts :=
    fun member => Set.disjoint_left.mp outside inside member
  apply edist_eq_zero.mp
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε positive _
  have positive_real : 0 < (ε : ℝ) := positive
  let δ : ℝ := (ε : ℝ) / 4
  have δpos : 0 < δ := div_pos positive_real (by norm_num)
  obtain ⟨u, inside_u, near_u⟩ := Metric.mem_closure_iff.mp (regular i x) δ δpos
  obtain ⟨v, inside_v, near_v⟩ := Metric.mem_closure_iff.mp (regular j y) δ δpos
  let U : interior s := ⟨u, interior_included i inside_u⟩
  let V : interior s := ⟨v, interior_included j inside_v⟩
  let ucell : cells i := ⟨u, interior_subset inside_u⟩
  let vcell : cells j := ⟨v, interior_subset inside_v⟩
  have left : cutFromInterior cells closed cuts cover U =
      of (fun i => cells i) S.relation i ucell :=
    cutFromSubtype_eq_of_mem cells closed cuts cover _ (uncut U.property) i ucell.property
  have right : cutFromInterior cells closed cuts cover V =
      of (fun i => cells i) S.relation j vcell :=
    cutFromSubtype_eq_of_mem cells closed cuts cover _ (uncut V.property) j vcell.property
  have middle : edist (of (fun i => cells i) S.relation i ucell)
      (of (fun i => cells i) S.relation j vcell) = edist u v := by
    rw [← left, ← right, (cutFromInterior_isometry cells closed cuts convex cover convex_s
      cut_closed outside).edist_eq]
    rfl
  have uv : dist u v < 2 * δ := by
    have first : dist u x.val < δ := by rwa [dist_comm]
    have last : dist x.val v < δ := by rwa [same]
    linarith [dist_triangle u x.val v]
  have vu : dist v y.val < δ := by rwa [dist_comm]
  calc
    edist (of (fun i => cells i) S.relation i x)
        (of (fun i => cells i) S.relation j y) ≤
        edist (of (fun i => cells i) S.relation i x)
          (of (fun i => cells i) S.relation i ucell) +
        (edist (of (fun i => cells i) S.relation i ucell)
          (of (fun i => cells i) S.relation j vcell) +
        edist (of (fun i => cells i) S.relation j vcell)
          (of (fun i => cells i) S.relation j y)) :=
      (edist_triangle _ _ _).trans (add_le_add le_rfl (edist_triangle _ _ _))
    _ = ENNReal.ofReal (dist x.val u + (dist u v + dist v y.val)) := by
      rw [(S.of_isometry i).edist_eq, (S.of_isometry j).edist_eq, middle]
      change edist x.val u + (edist u v + edist v y.val) = _
      rw [edist_dist, edist_dist, edist_dist,
        ← ENNReal.ofReal_add dist_nonneg dist_nonneg,
        ← ENNReal.ofReal_add dist_nonneg (add_nonneg dist_nonneg dist_nonneg)]
    _ ≤ ENNReal.ofReal (ε : ℝ) := by
      apply ENNReal.ofReal_le_ofReal
      dsimp [δ] at near_u uv vu
      linarith
    _ = 0 + (ε : ℝ≥0∞) := by simp


/-- Removing only boundary attachments leaves the exact intrinsic convex-region metric.
This includes unbounded cells and regions; no development or fan certificate is assumed. -/
def boundaryCutIsometryEquiv (convex : ∀ i, Convex ℝ (cells i))
    (full : ∀ i, (interior (cells i)).Nonempty) (cover : s = ⋃ i, cells i)
    (convex_s : Convex ℝ s) (cut_closed : IsClosed cuts)
    (outside : Disjoint (interior s) cuts) :
    PolygonalCut cells closed cuts ≃ᵢ PolygonalPoint s :=
  (changeSeamsIsometryEquiv (fun i => cells i)
    (fun _a _b joined => point_eq_of_glue _
      ((cutSeams cells closed cuts).physical_eq_of_eqvGen (Relation.EqvGen.rel _ _ joined)))
    (fun a b joined => cut_of_eq_of_boundary_cuts cells closed cuts convex full cover convex_s
      cut_closed outside a.2 b.2 joined)).trans
    (closedCoverIsometryEquiv cells closed convex cover)

/-- The constructed isometry is the actual physical cut-restoration map. -/
theorem boundaryCutIsometryEquiv_apply (convex : ∀ i, Convex ℝ (cells i))
    (full : ∀ i, (interior (cells i)).Nonempty) (cover : s = ⋃ i, cells i)
    (convex_s : Convex ℝ s) (cut_closed : IsClosed cuts)
    (outside : Disjoint (interior s) cuts) (x : PolygonalCut cells closed cuts) :
    boundaryCutIsometryEquiv cells closed cuts convex full cover convex_s cut_closed outside x =
      cutToPolygonal cells closed cuts convex cover x := by
  obtain ⟨a, rfl⟩ := point_surjective (fun i => cells i) (cutSeams cells closed cuts).relation x
  rfl

/-- Physical restoration is globally isometric when cuts stay on the boundary. -/
theorem cutToPolygonal_isometry_of_boundary_cuts (convex : ∀ i, Convex ℝ (cells i))
    (full : ∀ i, (interior (cells i)).Nonempty) (cover : s = ⋃ i, cells i)
    (convex_s : Convex ℝ s) (cut_closed : IsClosed cuts)
    (outside : Disjoint (interior s) cuts) :
    Isometry (cutToPolygonal cells closed cuts convex cover) := by
  have agrees := funext
    (boundaryCutIsometryEquiv_apply cells closed cuts convex full cover convex_s cut_closed outside)
  rw [← agrees]
  exact (boundaryCutIsometryEquiv cells closed cuts convex full cover convex_s
    cut_closed outside).isometry

end Unfoldings.MetricGluing
