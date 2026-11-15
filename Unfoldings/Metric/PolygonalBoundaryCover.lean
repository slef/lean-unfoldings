module

public import Unfoldings.Metric.PolygonalCoverGluing
public import Unfoldings.Metric.ChangeSeams
public import Unfoldings.Metric.Local

/-! Actual boundary seams for closed convex covers with disjoint interiors. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (cells : I → Set E)

/-- Only different cells declare seams; within a cell every point already equals itself. -/
def distinctCoincident (x y : Total (fun i => cells i)) : Prop :=
  x.1 ≠ y.1 ∧ coincident cells x y

omit [NormedSpace ℝ E] in
theorem point_eq_of_coincident {x y : Total (fun i => cells i)}
    (equal : coincident cells x y) :
    point (fun i => cells i) (distinctCoincident cells) x =
      point (fun i => cells i) (distinctCoincident cells) y := by
  classical
  by_cases different : x.1 ≠ y.1
  · exact point_eq_of_glue _ ⟨different, equal⟩
  · obtain ⟨i, p⟩ := x
    obtain ⟨j, q⟩ := y
    have same : i = j := not_ne_iff.mp different
    subst j
    have identical : p = q := Subtype.ext equal
    subst q
    rfl

/-- Deleting all same-cell identity seams preserves every intrinsic distance. -/
def distinctCoincidentIsometryEquiv :
    Realization (fun i => cells i) (distinctCoincident cells) ≃ᵢ
      Realization (fun i => cells i) (coincident cells) :=
  changeSeamsIsometryEquiv (fun i => cells i)
    (fun _ _ joined => point_eq_of_glue _ joined.2)
    (fun _ _ joined => point_eq_of_coincident cells joined)

variable {s : Set E}

/-- An exact intrinsic model whose seam support can be confined to actual cell boundaries. -/
def boundaryCoverIsometryEquiv [Finite I] (closed : ∀ i, IsClosed (cells i))
    (convex : ∀ i, Convex ℝ (cells i)) (cover : s = ⋃ i, cells i) :
    Realization (fun i => cells i) (distinctCoincident cells) ≃ᵢ PolygonalPoint s :=
  (distinctCoincidentIsometryEquiv cells).trans
    (closedCoverIsometryEquiv cells closed convex cover)

@[simp] theorem boundaryCoverIsometryEquiv_of [Finite I]
    (closed : ∀ i, IsClosed (cells i)) (convex : ∀ i, Convex ℝ (cells i))
    (cover : s = ⋃ i, cells i) (i : I) (x : cells i) :
    boundaryCoverIsometryEquiv cells closed convex cover
      (of (fun j => cells j) (distinctCoincident cells) i x) =
        PolygonalPoint.includeConvex (cells i) (cell_subset_of_cover cells cover i) x := rfl

omit [NormedSpace ℝ E] in
/-- Disjoint cell interiors and regular closedness exclude all interior seam points. -/
theorem distinctCoincident_seamSupport_boundary
    (regular : ∀ i, closure (interior (cells i)) = cells i)
    (disjoint : ∀ i j, i ≠ j → Disjoint (interior (cells i)) (interior (cells j)))
    (i : I) (x : cells i) (seam : x ∈ seamSupport (fun j => cells j) (distinctCoincident cells) i) :
    x.val ∉ interior (cells i) := by
  have separated (j : I) (different : i ≠ j) :
      Disjoint (interior (cells i)) (cells j) := by
    rw [← regular j]
    exact (disjoint i j different).closure_right isOpen_interior
  intro inside
  rcases seam with ⟨⟨j, y⟩, different, equal⟩ | ⟨⟨j, y⟩, different, equal⟩
  · exact Set.disjoint_left.mp (separated j different) inside (equal ▸ y.property)
  · exact Set.disjoint_left.mp (separated j (Ne.symm different)) inside (equal.symm ▸ y.property)

/-- The criterion applies directly to full-dimensional closed convex cells. -/
theorem distinctCoincident_seamSupport_boundary_of_convex
    (closed : ∀ i, IsClosed (cells i)) (convex : ∀ i, Convex ℝ (cells i))
    (full : ∀ i, (interior (cells i)).Nonempty)
    (disjoint : ∀ i j, i ≠ j → Disjoint (interior (cells i)) (interior (cells j)))
    (i : I) (x : cells i) (seam : x ∈ seamSupport (fun j => cells j) (distinctCoincident cells) i) :
    x.val ∉ interior (cells i) := by
  apply distinctCoincident_seamSupport_boundary cells _ disjoint i x seam
  intro j
  rw [(convex j).closure_interior_eq_closure_of_nonempty_interior (full j), (closed j).closure_eq]

end Unfoldings.MetricGluing
