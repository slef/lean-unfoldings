module

public import Unfoldings.Metric.PhysicalSeams
public import Unfoldings.Metric.PolygonalCoverGluing
public import Unfoldings.Metric.ChangeSeams

/-! Construct complete intrinsic cut spaces by closing the actual uncut cell attachments. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite I]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i)) (cuts : Set E)

/-- Close each actual uncut attachment separately. Point-only intersections on a cut
are removed; endpoints of retained seam intervals remain attached on their own sides. -/
def cutSeams : PhysicalSeams cells where
  carrier i j := closure ((cells i ∩ cells j) \ cuts)
  closed _ _ := isClosed_closure
  subset_left i _ := closure_minimal (fun _ hx => hx.1.1) (closed i)
  subset_right _ j := closure_minimal (fun _ hx => hx.1.2) (closed j)

/-- The complete cut space uses these exact closed seam pieces, without a development. -/
abbrev PolygonalCut := Realization (fun i => cells i) (cutSeams cells closed cuts).relation

omit [NormedSpace ℝ E] in
/-- Every original coincidence away from the cut set is still explicitly attached. -/
theorem cutSeams_related_of_physical_eq {a b : Total (fun i => cells i)}
    (same : a.2.val = b.2.val) (outside : a.2.val ∉ cuts) :
    (cutSeams cells closed cuts).relation a b := by
  refine ⟨(a.1, b.1), ⟨a.2.val, subset_closure ⟨⟨a.2.property, same ▸ b.2.property⟩, outside⟩⟩,
    ?_, ?_⟩
  · rfl
  · exact congrArg (Sigma.mk b.1) (Subtype.ext same.symm)

omit [NormedSpace ℝ E] in
theorem cutSeams_point_eq_of_physical_eq {a b : Total (fun i => cells i)}
    (same : a.2.val = b.2.val) (outside : a.2.val ∉ cuts) :
    point (fun i => cells i) (cutSeams cells closed cuts).relation a =
      point (fun i => cells i) (cutSeams cells closed cuts).relation b :=
  point_eq_of_glue _ (cutSeams_related_of_physical_eq cells closed cuts same outside)

omit [NormedSpace ℝ E] in
/-- Removing fewer physical points restores attachment pieces monotonically. -/
theorem cutSeams_relation_mono {other : Set E} (included : other ⊆ cuts) :
    ∀ a b, (cutSeams cells closed cuts).relation a b →
      (cutSeams cells closed other).relation a b := by
  apply PhysicalSeams.relation_mono
  intro i j
  apply closure_mono
  exact Set.sdiff_subset_sdiff_right included

variable {s : Set E}

/-- Restore the cuts into the actual intrinsic physical region. -/
def cutToPolygonal (convex : ∀ i, Convex ℝ (cells i)) (cover : s = ⋃ i, cells i) :
    PolygonalCut cells closed cuts → PolygonalPoint s :=
  lift (fun i => cells i) (cutSeams cells closed cuts).relation
    (fun i => PolygonalPoint.includeConvex (cells i) (cell_subset_of_cover cells cover i))
    (fun i => (PolygonalPoint.includeConvex_isometry (cells i) (convex i)
      (cell_subset_of_cover cells cover i)).lipschitzWith)
    (fun _ _ joined => PolygonalPoint.ext
      ((cutSeams cells closed cuts).physical_eq_of_eqvGen (Relation.EqvGen.rel _ _ joined)))

@[simp] theorem cutToPolygonal_of (convex : ∀ i, Convex ℝ (cells i))
    (cover : s = ⋃ i, cells i) (i : I) (p : cells i) :
    cutToPolygonal cells closed cuts convex cover
      (of (fun i => cells i) (cutSeams cells closed cuts).relation i p) =
        PolygonalPoint.includeConvex (cells i) (cell_subset_of_cover cells cover i) p := rfl

theorem cutToPolygonal_lipschitz (convex : ∀ i, Convex ℝ (cells i))
    (cover : s = ⋃ i, cells i) : LipschitzWith 1 (cutToPolygonal cells closed cuts convex cover) :=
  lift_lipschitz (fun i => cells i) (cutSeams cells closed cuts).relation _ _ _

theorem cutToPolygonal_surjective (convex : ∀ i, Convex ℝ (cells i))
    (cover : s = ⋃ i, cells i) :
    Function.Surjective (cutToPolygonal cells closed cuts convex cover) := by
  intro x
  have member : x.val ∈ ⋃ i, cells i := cover ▸ x.property
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
  exact ⟨of (fun i => cells i) (cutSeams cells closed cuts).relation i ⟨x.val, hi⟩,
    PolygonalPoint.ext rfl⟩

/-- All cut copies over an actual uncut point agree; distinct banks can occur only over cuts. -/
theorem cutToPolygonal_injective_off_cuts (convex : ∀ i, Convex ℝ (cells i))
    (cover : s = ⋃ i, cells i) {x y : PolygonalCut cells closed cuts}
    (same : cutToPolygonal cells closed cuts convex cover x =
      cutToPolygonal cells closed cuts convex cover y)
    (outside : (cutToPolygonal cells closed cuts convex cover x).val ∉ cuts) : x = y := by
  obtain ⟨a, rfl⟩ := point_surjective (fun i => cells i) (cutSeams cells closed cuts).relation x
  obtain ⟨b, rfl⟩ := point_surjective (fun i => cells i) (cutSeams cells closed cuts).relation y
  exact cutSeams_point_eq_of_physical_eq cells closed cuts
    (congrArg PolygonalPoint.val same) outside

/-- With no cuts this construction recovers exactly the original intrinsic region. -/
def uncutCoverIsometryEquiv (convex : ∀ i, Convex ℝ (cells i))
    (cover : s = ⋃ i, cells i) :
    PolygonalCut cells closed ∅ ≃ᵢ PolygonalPoint s :=
  (changeSeamsIsometryEquiv (fun i => cells i)
    (fun _ _ joined => point_eq_of_glue _
      ((cutSeams cells closed ∅).physical_eq_of_eqvGen (Relation.EqvGen.rel _ _ joined)))
    (fun _ _ joined => cutSeams_point_eq_of_physical_eq cells closed ∅ joined (by simp))).trans
    (closedCoverIsometryEquiv cells closed convex cover)

@[simp] theorem uncutCoverIsometryEquiv_point (convex : ∀ i, Convex ℝ (cells i))
    (cover : s = ⋃ i, cells i) (a : Total (fun i => cells i)) :
    (uncutCoverIsometryEquiv cells closed convex cover
      (point (fun i => cells i) (cutSeams cells closed ∅).relation a)).val = a.2.val := rfl

variable [CompleteSpace E]

omit [NormedSpace ℝ E] in
/-- Finitely many closed physical cells give a complete cut metric, including unbounded cuts. -/
theorem polygonalCut_complete : CompleteSpace (PolygonalCut cells closed cuts) :=
  (cutSeams cells closed cuts).completeSpace_realization closed

/-- The constructed metric topology agrees with the exact retained-attachment quotient. -/
def polygonalCutSeamHomeomorph :
    SeamQuotient (fun i => cells i) (cutSeams cells closed cuts).relation ≃ₜ
      PolygonalCut cells closed cuts :=
  (cutSeams cells closed cuts).seamHomeomorph closed

end Unfoldings.MetricGluing
