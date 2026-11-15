module

public import Unfoldings.Metric.PolygonalPiecewise
public import Unfoldings.Metric.Quotient

/-! Grouping convex cover cells into intrinsic polygonal pieces preserves the final glued metric. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing

variable {E I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (regions : I → Set E)

/-- Identify the actual physical points of the intrinsic pieces. -/
def polygonalCoincident (a b : Total (fun i => PolygonalPoint (regions i))) : Prop :=
  a.2.val = b.2.val

variable {s : Set E} (inside : ∀ i, regions i ⊆ s)

def groupedToPolygonal :
    Realization (fun i => PolygonalPoint (regions i)) (polygonalCoincident regions) →
      PolygonalPoint s :=
  lift _ _ (fun i => PolygonalPoint.inclusion (inside i))
    (fun i => PolygonalPoint.inclusion_lipschitz (inside i))
    (fun _ _ equal => PolygonalPoint.ext equal)

theorem groupedToPolygonal_lipschitz : LipschitzWith 1 (groupedToPolygonal regions inside) :=
  lift_lipschitz _ _ _ _ _

variable (cells : J → Set E) (owner : J → I) (contained : ∀ j, cells j ⊆ regions (owner j))
  (cover : s = ⋃ j, cells j)

/-- Choose a genuine physical cover cell and its containing intrinsic piece. -/
def groupedFromSubtype (x : s) :
    Realization (fun i => PolygonalPoint (regions i)) (polygonalCoincident regions) := by
  have member : ∃ j, x.val ∈ cells j := Set.mem_iUnion.mp (cover ▸ x.property)
  exact of _ _ (owner member.choose) ⟨x.val, contained member.choose member.choose_spec⟩

/-- Any intrinsic piece containing that physical point gives the same glued point. -/
theorem groupedFromSubtype_eq_of_mem (x : s) (i : I) (member : x.val ∈ regions i) :
    groupedFromSubtype regions cells owner contained cover x =
      of (fun i => PolygonalPoint (regions i)) (polygonalCoincident regions) i
        ⟨x.val, member⟩ := by
  unfold groupedFromSubtype
  exact point_eq_of_glue _ rfl

variable [Finite J] (closed : ∀ j, IsClosed (cells j)) (convex : ∀ j, Convex ℝ (cells j))

include closed convex in
/-- Convex cells control the inverse even when a containing region has reentrant corners. -/
theorem groupedFromPolygonal_lipschitz :
    LipschitzWith 1 (groupedFromSubtype regions cells owner contained cover ∘
      PolygonalPoint.toSubtype) := by
  apply PolygonalPoint.lipschitz_of_finite_closed_cover cells closed cover.le
  intro j x hx y hy
  rw [groupedFromSubtype_eq_of_mem regions cells owner contained cover x (owner j) (contained j hx),
    groupedFromSubtype_eq_of_mem regions cells owner contained cover y (owner j) (contained j hy)]
  have segment_inside := ((convex j).segment_subset hx hy).trans (contained j)
  have bound := of_lipschitz (fun i => PolygonalPoint (regions i)) (polygonalCoincident regions)
    (owner j) (⟨x.val, contained j hx⟩ : PolygonalPoint (regions (owner j)))
      (⟨y.val, contained j hy⟩ : PolygonalPoint (regions (owner j)))
  rw [PolygonalPoint.edist_eq_of_segment segment_inside] at bound
  exact bound

/-- Regrouping a finite closed convex cover into actual intrinsic pieces preserves the metric.
The pieces themselves may be nonconvex, unbounded or disconnected. -/
def groupedCoverIsometryEquiv :
    Realization (fun i => PolygonalPoint (regions i)) (polygonalCoincident regions) ≃ᵢ
      PolygonalPoint s := by
  let f := groupedToPolygonal regions inside
  let g := groupedFromSubtype regions cells owner contained cover ∘ PolygonalPoint.toSubtype
  have left : Function.LeftInverse g f := by
    intro x
    obtain ⟨⟨i, p⟩, rfl⟩ := point_surjective _ _ x
    exact groupedFromSubtype_eq_of_mem regions cells owner contained cover
      ⟨p.val, inside i p.property⟩ i p.property
  have right : Function.RightInverse g f := by
    intro x
    have member : x.val ∈ ⋃ j, cells j := cover ▸ x.property
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp member
    change groupedToPolygonal regions inside
      (groupedFromSubtype regions cells owner contained cover ⟨x.val, x.property⟩) = x
    rw [groupedFromSubtype_eq_of_mem regions cells owner contained cover
      ⟨x.val, x.property⟩ (owner j) (contained j hj)]
    exact PolygonalPoint.ext rfl
  refine ⟨⟨f, g, left, right⟩, ?_⟩
  intro x y
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using groupedToPolygonal_lipschitz regions inside x y
  · have bound := groupedFromPolygonal_lipschitz regions cells owner contained cover closed convex
      (f x) (f y)
    change edist (g (f x)) (g (f y)) ≤ (1 : ℝ≥0∞) * edist (f x) (f y) at bound
    simpa only [left x, left y, one_mul] using bound

@[simp] theorem groupedCoverIsometryEquiv_point
    (a : Total (fun i => PolygonalPoint (regions i))) :
    (groupedCoverIsometryEquiv regions inside cells owner contained cover closed convex
      (point _ (polygonalCoincident regions) a)).val = a.2.val := rfl

end Unfoldings.MetricGluing
