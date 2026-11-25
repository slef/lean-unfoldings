module

public import Unfoldings.Convex.SlopeReference

/-! The given outward normals of a polygon supply consistent side directions. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- A finite half-plane presentation with unit outward normals and a reference
slope strictly on the inner side of each supporting line. -/
structure PolygonSideDirections (I : Type*) (slopes : Set Plane) where
  normal : I → Plane
  offset : I → ℝ
  unit : ∀ i, ‖normal i‖ = 1
  reference : Plane
  strict : ∀ i, inner ℝ (normal i) reference < offset i
  carrier_eq : slopes = {p | ∀ i, inner ℝ (normal i) p ≤ offset i}

namespace PolygonSideDirections

variable {I : Type*} {slopes : Set Plane} (B : PolygonSideDirections I slopes)

theorem side_bound {p : Plane} (h : p ∈ slopes) (i : I) :
    inner ℝ (B.normal i) p ≤ B.offset i := B.carrier_eq.subset h i

include B in
theorem isClosed : IsClosed slopes := by
  rw [B.carrier_eq, show {p : Plane | ∀ i, inner ℝ (B.normal i) p ≤ B.offset i} =
      ⋂ i, {p : Plane | inner ℝ (B.normal i) p ≤ B.offset i} by ext p; simp]
  exact isClosed_iInter fun i => isClosed_le (continuous_const.inner continuous_id) continuous_const

include B in
theorem convex : Convex ℝ slopes := by
  rw [B.carrier_eq, show {p : Plane | ∀ i, inner ℝ (B.normal i) p ≤ B.offset i} =
      ⋂ i, {p : Plane | inner ℝ (B.normal i) p ≤ B.offset i} by ext p; simp]
  exact convex_iInter fun i =>
    convex_halfSpace_le (innerSL ℝ (B.normal i)).toLinearMap.isLinear _

variable [Finite I]

theorem exists_active_side {p : Plane} (h : p ∈ frontier slopes) :
    ∃ i, inner ℝ (B.normal i) p = B.offset i := by
  classical
  have member := B.isClosed.frontier_subset h
  by_contra! missing
  have strict : ∀ i, inner ℝ (B.normal i) p < B.offset i :=
    fun i => (B.side_bound member i).lt_of_ne (missing i)
  have open_set : IsOpen (⋂ i, {q : Plane | inner ℝ (B.normal i) q < B.offset i}) :=
    isOpen_iInter_of_finite fun i =>
      isOpen_lt (continuous_const.inner continuous_id) continuous_const
  exact h.2 (open_set.subset_interior_iff.mpr (fun q hq =>
    B.carrier_eq.symm.subset fun i => (Set.mem_iInter.mp hq i).le) (Set.mem_iInter.mpr strict))

include B in
theorem reference_mem_interior : B.reference ∈ interior slopes := by
  let strictSides := ⋂ i, {p : Plane | inner ℝ (B.normal i) p < B.offset i}
  have opens : IsOpen strictSides := isOpen_iInter_of_finite fun i =>
    isOpen_lt (continuous_const.inner continuous_id) continuous_const
  have contained : strictSides ⊆ slopes := by
    intro p member
    exact B.carrier_eq.symm.subset fun i => (Set.mem_iInter.mp member i).le
  exact opens.subset_interior_iff.mpr contained (Set.mem_iInter.mpr B.strict)

variable [Nonempty I]

open Classical in
/-- Choose one side for each boundary slope. In particular, every occurrence
of a polygon corner uses the same direction. -/
def sideIndex (p : Plane) : I :=
  if h : p ∈ frontier slopes then (B.exists_active_side h).choose else Classical.choice ‹_›

theorem sideIndex_active {p : Plane} (h : p ∈ frontier slopes) :
    inner ℝ (B.normal (B.sideIndex p)) p = B.offset (B.sideIndex p) := by
  classical
  rw [sideIndex, dif_pos h]
  exact (B.exists_active_side h).choose_spec

/-- A consistently assigned polygon side is a positive support direction for
every root's active slope. -/
def exteriorPlan {E : SlopeEnvelope} (domain : E.slopes = slopes) {V : Type*}
    (point : V → Plane) (injective : Function.Injective point) (slope : V → Plane)
    (active : ∀ v, E.Active (point v) (slope v)) (boundary : ∀ v, slope v ∈ frontier slopes) :
    (E.recenter B.reference).ExteriorPlan V where
  point := point
  point_injective := injective
  slope v := slope v - B.reference
  direction p := B.normal (B.sideIndex (p + B.reference))
  active v := (E.recenter_active_iff B.reference).mpr (active v)
  unit v := B.unit _
  positive v := by
    rw [sub_add_cancel, inner_sub_right, B.sideIndex_active (boundary v)]
    exact sub_pos.mpr (B.strict _)
  support v := by
    rw [sub_add_cancel]
    apply E.recenter_support B.reference
    intro q h
    rw [B.sideIndex_active (boundary v)]
    exact B.side_bound (domain ▸ h) _

end PolygonSideDirections
end Unfoldings
