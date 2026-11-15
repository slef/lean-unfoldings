module

public import Unfoldings.Metric.PolygonalPiecewise
public import Unfoldings.Metric.PolygonalClosedCover
public import Unfoldings.Metric.Quotient

/-! Gluing a finite closed convex cover recovers the actual intrinsic polygonal space. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (cells : I → Set E)

/-- Identify actual coincident points, including points on redundant covering cells. -/
def coincident (x y : Total (fun i => cells i)) : Prop := x.2.val = y.2.val

variable {s : Set E}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Every covering cell lies in the original physical region. -/
theorem cell_subset_of_cover (cover : s = ⋃ i, cells i) (i : I) : cells i ⊆ s := by
  rw [cover]
  exact Set.subset_iUnion _ i

/-- The canonical physical map from the glued cells into the intrinsic region. -/
def coverToPolygonal (convex : ∀ i, Convex ℝ (cells i))
    (cover : s = ⋃ i, cells i) :
    Realization (fun i => cells i) (coincident cells) → PolygonalPoint s :=
  lift (fun i => cells i) (coincident cells)
    (fun i => PolygonalPoint.includeConvex (cells i) (cell_subset_of_cover cells cover i))
    (fun i => (PolygonalPoint.includeConvex_isometry (cells i) (convex i)
      (cell_subset_of_cover cells cover i)).lipschitzWith)
    (fun _ _ equal => PolygonalPoint.ext equal)

@[simp] theorem coverToPolygonal_of (convex : ∀ i, Convex ℝ (cells i))
    (cover : s = ⋃ i, cells i) (i : I) (x : cells i) :
    coverToPolygonal cells convex cover (of (fun i => cells i) (coincident cells) i x) =
      PolygonalPoint.includeConvex (cells i) (cell_subset_of_cover cells cover i) x := rfl

theorem coverToPolygonal_lipschitz (convex : ∀ i, Convex ℝ (cells i))
    (cover : s = ⋃ i, cells i) : LipschitzWith 1 (coverToPolygonal cells convex cover) :=
  lift_lipschitz (fun i => cells i) (coincident cells) _ _ _

/-- A cell representative of an actual point. All choices agree in the realization. -/
def coverFromSubtype (cover : s = ⋃ i, cells i) (x : s) :
    Realization (fun i => cells i) (coincident cells) := by
  have present : ∃ i, x.val ∈ cells i := Set.mem_iUnion.mp (cover ▸ x.property)
  exact of (fun i => cells i) (coincident cells) present.choose
    ⟨x.val, present.choose_spec⟩

omit [NormedSpace ℝ E] in
theorem coverFromSubtype_eq_of_mem (cover : s = ⋃ i, cells i) (x : s)
    (i : I) (member : x.val ∈ cells i) :
    coverFromSubtype cells cover x =
      of (fun i => cells i) (coincident cells) i ⟨x.val, member⟩ := by
  unfold coverFromSubtype
  apply point_eq_of_glue
  rfl

/-- The inverse on the actual intrinsic point type, independent of cell choices. -/
def coverFromPolygonal (cover : s = ⋃ i, cells i) :
    PolygonalPoint s → Realization (fun i => cells i) (coincident cells) :=
  coverFromSubtype cells cover ∘ PolygonalPoint.toSubtype

theorem coverFromPolygonal_lipschitz [Finite I]
    (closed : ∀ i, IsClosed (cells i)) (cover : s = ⋃ i, cells i) :
    LipschitzWith 1 (coverFromPolygonal cells cover) := by
  apply PolygonalPoint.lipschitz_of_finite_closed_cover cells closed cover.le
  intro i x hx y hy
  rw [coverFromSubtype_eq_of_mem cells cover x i hx,
    coverFromSubtype_eq_of_mem cells cover y i hy]
  exact (of_lipschitz (fun i => cells i) (coincident cells) i).edist_le_mul
    ⟨x.val, hx⟩ ⟨y.val, hy⟩

theorem coverToPolygonal_leftInverse (convex : ∀ i, Convex ℝ (cells i))
    (cover : s = ⋃ i, cells i) :
    Function.LeftInverse (coverFromPolygonal cells cover)
      (coverToPolygonal cells convex cover) := by
  intro x
  obtain ⟨⟨i, p⟩, rfl⟩ := point_surjective (fun i => cells i) (coincident cells) x
  change coverFromSubtype cells cover
    ⟨p.val, cell_subset_of_cover cells cover i p.property⟩ = _
  exact coverFromSubtype_eq_of_mem cells cover _ i p.property

theorem coverToPolygonal_rightInverse (convex : ∀ i, Convex ℝ (cells i))
    (cover : s = ⋃ i, cells i) :
    Function.RightInverse (coverFromPolygonal cells cover)
      (coverToPolygonal cells convex cover) := by
  intro x
  have member : x.val ∈ ⋃ i, cells i := cover ▸ x.property
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
  change coverToPolygonal cells convex cover
    (coverFromSubtype cells cover ⟨x.val, x.property⟩) = x
  rw [coverFromSubtype_eq_of_mem cells cover _ i hi]
  exact PolygonalPoint.ext rfl

/-- Finite closed convex covers recover exactly the intrinsic metric, even with
unbounded or redundant cells. No separation or exactness premise is needed. -/
def closedCoverIsometryEquiv [Finite I] (closed : ∀ i, IsClosed (cells i))
    (convex : ∀ i, Convex ℝ (cells i)) (cover : s = ⋃ i, cells i) :
    Realization (fun i => cells i) (coincident cells) ≃ᵢ PolygonalPoint s where
  toFun := coverToPolygonal cells convex cover
  invFun := coverFromPolygonal cells cover
  left_inv := coverToPolygonal_leftInverse cells convex cover
  right_inv := coverToPolygonal_rightInverse cells convex cover
  isometry_toFun := by
    intro x y
    apply le_antisymm
    · simpa only [ENNReal.coe_one, one_mul] using
        coverToPolygonal_lipschitz cells convex cover x y
    · have bound := coverFromPolygonal_lipschitz cells closed cover
        (coverToPolygonal cells convex cover x) (coverToPolygonal cells convex cover y)
      simpa only [coverToPolygonal_leftInverse cells convex cover x,
        coverToPolygonal_leftInverse cells convex cover y, ENNReal.coe_one, one_mul]
        using bound

/-- Coincident-cell gluings make no additional zero-distance identifications. -/
theorem coincident_exact (convex : ∀ i, Convex ℝ (cells i))
    (cover : s = ⋃ i, cells i) : Exact (fun i => cells i) (coincident cells) := by
  intro x y equal
  apply Relation.EqvGen.rel
  have physical := congrArg (coverToPolygonal cells convex cover) equal
  exact congrArg PolygonalPoint.val physical

end Unfoldings.MetricGluing
