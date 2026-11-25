module

public import Unfoldings.FewestNets.ThreeExitEmbedding
public import Unfoldings.Geometry.OrientedHistory
public import Unfoldings.FewestNets.ThreeExitHistoryBounds
public import Unfoldings.Geometry.ComplexFrameSubhistories

/-! Every fine history shares the same original root, sign, and eventual exit. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting

open FewestNets Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty}
  {H : ThreeExitStemWindows}
  (R : K.ThreeExitComponentRouting seed B compact nonempty H)

local notation "U" => K.selectionComponent slopes seed
local notation "S" => K.restrictedCarrier U
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ S}
local notation "A" => R.stems.choice.parents
local notation "P" => R.truncatedParents
local notation "Root" => {r : V // r ∈ AscendingParents.roots A}
local notation "G" => SlopeEnvelope.recenter
  (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty) B.reference
local notation "p" => (fun v : V => K.projectedVertex (Subtype.val v))

/-- Name the original frontier root on both the stems and their added exits. -/
def cutRoot : (A).LeafVertex → Root
  | .inl v => ⟨(A).root v, (A).root_mem v⟩
  | .inr r => r

theorem cutRoot_parent (v : (A).LeafVertex) (nonroot : v ∉ (P).roots) :
    R.cutRoot v = R.cutRoot ((P).parent v) := by
  cases v with
  | inr r => exact (nonroot ⟨r, rfl⟩).elim
  | inl v =>
    by_cases root : v ∈ (A).roots
    · let r : Root := ⟨v, root⟩
      change R.cutRoot (.inl r.val) = R.cutRoot
        (((A).withLeaves R.leafRank R.height_lt_leafRank).parent (.inl r.val))
      rw [(A).withLeaves_parent_root R.leafRank R.height_lt_leafRank r]
      exact Subtype.ext ((A).root_of_root root)
    · change R.cutRoot (.inl v) = R.cutRoot
        (((A).withLeaves R.leafRank R.height_lt_leafRank).parent (.inl v))
      rw [(A).withLeaves_parent_nonroot R.leafRank R.height_lt_leafRank root]
      exact Subtype.ext ((A).root_eq_of_ancestor ((A).ancestor_parent v))

open Classical in
/-- Use the reflected chart just when this whole tree takes the west option. -/
def rootHeadingChart (r : Root) : Plane ≃ₗᵢ[ℝ] ℂ :=
  exitHeadingChart (if R.stems.choice.choosesEast r.val then false else true)

open Classical in
def rootWindowStart (r : Root) : ℝ :=
  if R.stems.choice.choosesEast r.val then H.eastStart else H.westStart

def rootExitDirection (r : Root) : Plane :=
  R.exits.direction (R.exits.slope (R.exitRoot r))

theorem rootExitDirection_ne_zero (r : Root) : R.rootExitDirection r ≠ 0 :=
  norm_ne_zero_iff.mp (by
    change ‖R.exits.direction (R.exits.slope (R.exitRoot r))‖ ≠ 0
    rw [R.exits.unit]
    exact one_ne_zero)

variable (level : ℝ)

/-- Every coarse edge is in the stem window of its root or has the exact
terminal heading at that root. -/
theorem coarse_direction_in_root_window
    (higher : ∀ v : V, (G).height (p v) < level) (v : V) :
    let r := R.cutRoot (.inl v)
    let L := R.rootHeadingChart r
    let lo := R.rootWindowStart r
    (L (R.cutLast level v - p v)).arg ∈ Set.Icc lo (lo + H.width) ∨
      (L (R.cutLast level v - p v)).arg = (L (R.rootExitDirection r)).arg := by
  classical
  dsimp only
  by_cases root : v ∈ (A).roots
  · right
    let r : Root := ⟨v, root⟩
    have owner : R.cutRoot (.inl v) = r := Subtype.ext ((A).root_of_root root)
    rw [owner, R.cutLast_exit level r]
    have origin : R.exits.point (R.exitRoot r) = p v := R.point_eq _
    have along :
        R.exits.pointAtLevel level (R.exitRoot r) - p v =
          R.exits.timeAtLevel level (R.exitRoot r) • R.rootExitDirection r := by
      rw [SlopeEnvelope.ExteriorPlan.pointAtLevel, SlopeEnvelope.ExteriorPlan.ray, origin,
        add_sub_cancel_left]
      rfl
    rw [along, map_smul]
    change Complex.arg ((R.exits.timeAtLevel level (R.exitRoot r) : ℂ) *
      R.rootHeadingChart r (R.rootExitDirection r)) = _
    exact Complex.arg_real_mul _ (R.exits.timeAtLevel_pos level _ (R.exit_origin_below level higher r))
  · left
    rw [R.cutLast_interior_stem level root, R.stems.choice.parent_eq v root]
    have sign := R.stems.choice.choosesEast_ancestor_iff ((A).ancestor_root v)
    change R.stems.choice.choosesEast (R.cutRoot (.inl v)).val ↔ R.stems.choice.choosesEast v at sign
    by_cases east : R.stems.choice.choosesEast v
    · have root_east := sign.mpr east
      simpa only [rootHeadingChart, rootWindowStart, ite_eq_left root_east, ite_eq_left east]
        using R.stems.east_heading v root
    · have root_west : ¬ R.stems.choice.choosesEast (R.cutRoot (.inl v)).val :=
        fun h => east (sign.mp h)
      simpa only [rootHeadingChart, rootWindowStart, ite_eq_right root_west, ite_eq_right east]
        using R.stems.west_heading v root

/-- All directions in a refined directed history lie in its one stem window
or have its root's single exit heading. -/
theorem exists_root_window_for_fine_history
    (higher : ∀ v : V, (G).height (p v) < level)
    {n : ℕ} (positive : 0 < n) (path : PolygonalChain Plane n)
    (aligned : ∀ i : Fin n, Nonempty ((R.truncatedEmbedding level higher).OrientedSubsegment
      (path.vertex i.castSucc) (path.vertex i.succ))) :
    ∃ r : Root, ∀ i,
      ((R.rootHeadingChart r) (path.edge i)).arg ∈
        Set.Icc (R.rootWindowStart r) (R.rootWindowStart r + H.width) ∨
      ((R.rootHeadingChart r) (path.edge i)).arg =
        ((R.rootHeadingChart r) (R.rootExitDirection r)).arg := by
  classical
  let graph := R.truncatedEmbedding level higher
  let subedge (i : Fin n) := Classical.choice (aligned i)
  let r := R.cutRoot (graph.left (subedge ⟨0, positive⟩).edge)
  have along (e : {v // v ∉ (P).roots}) :
      R.cutRoot (graph.left e) = R.cutRoot (graph.right e) :=
    R.cutRoot_parent e.val e.property
  have same (i : Fin n) : R.cutRoot (graph.left (subedge i).edge) = r :=
    FiniteEmbeddedGraph.chain_labels_const R.cutRoot along
      (R.truncatedEmbedding_straight level higher) positive path subedge i
  refine ⟨r, fun i => ?_⟩
  have geometry := (subedge i).displacement
  change path.edge i =
    ((subedge i).last - (subedge i).first) •
      (graph.vertex (graph.right (subedge i).edge) - graph.vertex (graph.left (subedge i).edge))
    at geometry
  have time := sub_pos.mpr (subedge i).increasing
  cases kind : (subedge i).edge.val with
  | inr root => exact ((subedge i).edge.property ⟨root, kind.symm⟩).elim
  | inl v =>
    let e : {v // v ∉ (P).roots} := ⟨.inl v,
      (A).withLeaves_inl_nonroot R.leafRank R.height_lt_leafRank v⟩
    have edge_eq : (subedge i).edge = e := Subtype.ext kind
    rw [edge_eq] at geometry
    change path.edge i =
      ((subedge i).last - (subedge i).first) • (R.cutLast level v - p v) at geometry
    have owner := same i
    rw [edge_eq] at owner
    change R.cutRoot (.inl v) = r at owner
    have stem := R.coarse_direction_in_root_window level higher v
    dsimp only at stem
    rw [owner] at stem
    have heading : ((R.rootHeadingChart r) (path.edge i)).arg =
        ((R.rootHeadingChart r) (R.cutLast level v - p v)).arg := by
      rw [geometry, map_smul]
      exact Complex.arg_real_mul _ time
    rw [heading]
    exact stem

/-- A directed fine history satisfies both length and radial inequalities for
every actual subpath, using the common aperture certified at its exits. -/
theorem fine_history_bounds (higher : ∀ v : V, (G).height (p v) < level)
    {n : ℕ} (positive : 0 < n) (path : PolygonalChain Plane n)
    (aligned : ∀ i : Fin n, Nonempty ((R.truncatedEmbedding level higher).OrientedSubsegment
      (path.vertex i.castSucc) (path.vertex i.succ)))
    {width : ℝ} (acute : width ≤ π / 2)
    (span : ∀ r : Root,
      let exit := ((R.rootHeadingChart r) (R.rootExitDirection r)).arg
      let lo := R.rootWindowStart r
      max (lo + H.width) exit - min lo exit ≤ width)
    (j : Fin (n + 1)) (i : Fin n) (earlier : j.val ≤ i.val) :
    let length := (path.interval j.val (i.val - j.val) (by omega)).projectedLength
    let chord := path.vertex i.castSucc - path.vertex j
    length ≤ √2 * ‖chord‖ ∧ cos width * (‖chord‖ * ‖path.edge i‖) ≤
      inner ℝ chord (path.edge i) := by
  obtain ⟨r, headings⟩ := R.exists_root_window_for_fine_history level higher positive path aligned
  let L := R.rootHeadingChart r
  let direction := L (R.rootExitDirection r)
  have genuine : direction ≠ 0 :=
    fun same => R.rootExitDirection_ne_zero r (L.map_eq_zero_iff.mp same)
  have bounds := threeExit_history_bounds (path.inComplexFrame L) direction acute genuine (span r)
    (fun k _ => by simpa only [path.inComplexFrame_edge L k] using headings k) j i earlier
  simp only [PolygonalChain.inComplexFrame_chord_inner] at bounds
  simpa only [PolygonalChain.inComplexFrame_interval_projectedLength,
    PolygonalChain.inComplexFrame_norm_sub, PolygonalChain.inComplexFrame_edge,
    LinearIsometryEquiv.norm_map] using bounds

end Unfoldings.ConvexRoof.ThreeExitComponentRouting
