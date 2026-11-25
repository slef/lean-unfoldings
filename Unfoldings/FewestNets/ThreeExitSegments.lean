module

public import Unfoldings.FewestNets.ThreeExitRouting
public import Unfoldings.Convex.ExteriorRayLevel
public import Unfoldings.Topology.ParentLeaves

/-! The three-exit forest truncates at the actual physical section of the clipped roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : FewestNets.ThreeExitStemWindows}
  (R : K.ThreeExitComponentRouting seed B compact nonempty H)

local notation "U" => K.selectionComponent slopes seed
local notation "S" => K.restrictedCarrier U
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ S}
local notation "A" => R.stems.choice.parents
local notation "G" => K.componentClippedExtension
  (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty
local notation "p" => (fun v : V => K.projectedVertex (Subtype.val v))

theorem root_frontier (r : {v // v ∈ (A).roots}) : p r.val ∈ frontier S :=
  R.stems.roots_eq.subset r.property

/-- The root of an original parent tree has one corresponding exterior ray. -/
def exitRoot (r : {v // v ∈ (A).roots}) :
    {v : C.Vertex Set.univ // K.projectedVertex v ∈ frontier S} :=
  ⟨r.val.val, R.root_frontier r⟩

def leafRank : ℝ := by
  classical
  exact (∑ v : V, |(A).height v|) + 1

theorem height_lt_leafRank (v : V) : (A).height v < R.leafRank := by
  classical
  have bound := Finset.single_le_sum (s := Finset.univ) (f := fun v : V => |(A).height v|)
    (fun w _ => abs_nonneg ((A).height w)) (Finset.mem_univ v)
  exact ((le_abs_self _).trans bound).trans_lt (lt_add_one _)

/-- The graph order uses the north coordinate on the original component.
The leaf rank is independent of the physical truncation height. -/
def truncatedParents : AscendingParents (A).LeafVertex :=
  (A).withLeaves R.leafRank R.height_lt_leafRank

variable (level : ℝ)

def truncatedPoint : (A).LeafVertex → Plane
  | .inl v => p v
  | .inr r => R.exits.pointAtLevel level (R.exitRoot r)

def cutLast (v : V) : Plane := R.truncatedPoint level (R.truncatedParents.parent (.inl v))

theorem cutLast_interior_stem {v : V} (h : v ∉ (A).roots) :
    R.cutLast level v = p ((A).parent v) := by
  unfold cutLast truncatedParents
  rw [(A).withLeaves_parent_nonroot R.leafRank R.height_lt_leafRank h]
  rfl

theorem cutLast_exit (r : {v // v ∈ (A).roots}) :
    R.cutLast level r.val = R.exits.pointAtLevel level (R.exitRoot r) := by
  unfold cutLast truncatedParents
  rw [(A).withLeaves_parent_root R.leafRank R.height_lt_leafRank r]
  rfl

theorem stem_segment_subset {v : V} (h : v ∉ (A).roots) :
    segment ℝ (p v) (R.cutLast level v) ⊆ S := by
  classical
  rw [R.cutLast_interior_stem level h, R.stems.choice.parent_eq v h]
  by_cases east : R.stems.choice.choosesEast v
  · simpa only [ite_eq_left east] using R.stems.east_segment v h
  · simpa only [ite_eq_right east] using R.stems.west_segment v h

theorem exists_truncation_level : ∃ level : ℝ, ∀ v : V, (G).height (p v) < level := by
  classical
  let h (v : V) := |(G).height (p v)|
  refine ⟨(∑ v : V, h v) + 1, fun v => ?_⟩
  have bound := Finset.single_le_sum (s := Finset.univ) (f := h)
    (fun w _ => abs_nonneg ((G).height (p w))) (Finset.mem_univ v)
  exact ((le_abs_self _).trans bound).trans_lt (lt_add_one _)

theorem exit_origin_below
    (higher : ∀ v : V, (G).height (p v) < level) (r : {v // v ∈ (A).roots}) :
    (G).height (R.exits.point (R.exitRoot r)) < level := by
  rw [R.point_eq]
  exact higher r.val

theorem cutLast_height_le
    (higher : ∀ v : V, (G).height (p v) < level) (v : V) : (G).height (R.cutLast level v) ≤ level := by
  by_cases root : v ∈ (A).roots
  · let r : {v // v ∈ (A).roots} := ⟨v, root⟩
    change (G).height (R.cutLast level r.val) ≤ level
    rw [R.cutLast_exit level r,
      R.exits.pointAtLevel_height level _ (R.exit_origin_below level higher r)]
  · rw [R.cutLast_interior_stem level root]
    exact (higher _).le

theorem cutLast_ne_cutFirst
    (higher : ∀ v : V, (G).height (p v) < level) (v : V) : p v ≠ R.cutLast level v := by
  by_cases root : v ∈ (A).roots
  · intro equal
    have height := congrArg (G).height equal
    let r : {v // v ∈ (A).roots} := ⟨v, root⟩
    change (G).height (p v) = (G).height (R.cutLast level r.val) at height
    rw [R.cutLast_exit level r,
      R.exits.pointAtLevel_height level _ (R.exit_origin_below level higher r)] at height
    exact (higher v).ne height
  · intro equal
    rw [R.cutLast_interior_stem level root] at equal
    have same : v = (A).parent v :=
      Subtype.ext (K.projectedVertex_injective equal)
    have up := (A).ascending v root
    rw [← same] at up
    exact (lt_irrefl _ up)

end Unfoldings.ConvexRoof.ThreeExitComponentRouting
