module

public import Unfoldings.FewestNets.RevisedLatitudeAnnularChart
public import Unfoldings.FewestNets.RevisedLatitudeSouthSelector
public import Unfoldings.Cap.GnomonicArea
public import Unfoldings.Geometry.SpatialRotationSphere

/-! The geometric selectors are the actual annular triangles and the two grouped polar fans. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real Cap Module MeasureTheory
open AcuteLatitudeGrid (polarFrame polarReflection polarRadius)

abbrev ChordFace (a : ℝ) := (rings a).ChordFace

/-- The two polar cells and the individual annular triangles. -/
abbrev Selector (a : ℝ) := Fin 2 ⊕ AnnularTriangle a

/-- Read the selected polygon of each original chord triangle. -/
def chordSelector {a : ℝ} : ChordFace a → Selector a
  | .inl _ => .inl 0
  | .inr (.inl i) => .inr i
  | .inr (.inr _) => .inl 1

/-- Put the center of the chosen selector at the north pole of its own chart. -/
def selectorFrame {a : ℝ} : Selector a → Space ≃ₗᵢ[ℝ] Space
  | .inl p => if p = 0 then LinearIsometryEquiv.refl ℝ Space else polarReflection
  | .inr i => annularChartFrame a i

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

local notation "B" => LatitudeRings.chordBasis (rings_oriented positive small)

/-- The actual slope polygon in the selector's own chart. -/
def selectorSlopes : Selector a → Set Plane
  | .inl _ => regularSlopePolygon polarFrame (rowSize a 0) (tan (polarRadius a))
  | .inr i => annularSlopeSelector positive small i

/-- The normal directions of a selector, in the original common sphere. -/
def selectorSphere (i : Selector a) : Set Space :=
  selectorFrame i ⁻¹' (gnomonicNormal '' selectorSlopes positive small i)

/-- Membership in a spherical selector is exactly membership in one of its actual chord triangles. -/
theorem mem_selectorSphere_iff (k : Selector a) (p : Space) :
    p ∈ selectorSphere positive small k ↔ ‖p‖ = 1 ∧
      ∃ i : ChordFace a, chordSelector i = k ∧ ∀ j, 0 ≤ (B i).coord j p := by
  rcases k with pole | i
  · fin_cases pole
    · change p ∈ gnomonicNormal '' regularSlopePolygon
        polarFrame (rowSize a 0) (tan (polarRadius a)) ↔ _
      rw [northPolarSelector_eq_chordFan positive small, Set.mem_iUnion]
      constructor
      · rintro ⟨e, unit, coord⟩
        exact ⟨unit, .inl e, rfl, coord⟩
      · rintro ⟨unit, e, tag, coord⟩
        rcases e with e | e | e
        · exact ⟨e, unit, coord⟩
        · cases tag
        · cases tag
    · change p ∈ polarReflection ⁻¹' (gnomonicNormal '' regularSlopePolygon
        polarFrame (rowSize a 0) (tan (polarRadius a))) ↔ _
      rw [southPolarSelector_eq_chordFan positive small, Set.mem_iUnion]
      constructor
      · rintro ⟨e, unit, coord⟩
        exact ⟨unit, .inr (.inr e), rfl, coord⟩
      · rintro ⟨unit, e, tag, coord⟩
        rcases e with e | e | e
        · cases tag
        · cases tag
        · exact ⟨e, unit, coord⟩
  · change p ∈ annularChartFrame a i ⁻¹' (gnomonicNormal '' annularSlopeSelector positive small i) ↔ _
    rw [annularSlopeSelector_eq_chord positive small]
    constructor
    · rintro ⟨unit, coord⟩
      exact ⟨unit, .inr (.inl i), rfl, coord⟩
    · rintro ⟨unit, e, tag, coord⟩
      rcases e with e | e | e
      · cases tag
      · have same : e = i := Sum.inr.inj tag
        subst e
        exact ⟨unit, coord⟩
      · cases tag

/-- Every unit normal belongs to some actual polygon selector. -/
theorem exists_selectorSphere (p : Space) (unit : ‖p‖ = 1) :
    ∃ k, p ∈ selectorSphere positive small k := by
  let x : Metric.sphere (0 : Space) 1 := ⟨p, Metric.mem_sphere.mpr ((dist_zero_right p).trans unit)⟩
  have cover := (LatitudeRings.chordSphere_partition (rings_oriented positive small)).1
  have exists_chord : x ∈ ⋃ i, chordTriangleOnSphere (B i) := cover.symm ▸ Set.mem_univ x
  obtain ⟨i, coords⟩ := Set.mem_iUnion.mp exists_chord
  exact ⟨chordSelector i, (mem_selectorSphere_iff positive small _ _).mpr ⟨unit, i, rfl, coords⟩⟩

/-- Away from the finitely many original supporting edge planes, the cell label is unique. -/
theorem selectorSphere_unique {p : Space} {i j : Selector a}
    (first : p ∈ selectorSphere positive small i) (last : p ∈ selectorSphere positive small j)
    (regular : ∀ (c : ChordFace a) k, (B c).coord k p ≠ 0) : i = j := by
  obtain ⟨unit, b, bi, hb⟩ := (mem_selectorSphere_iff positive small i p).mp first
  obtain ⟨_, c, cj, hc⟩ := (mem_selectorSphere_iff positive small j p).mp last
  have same : b = c := by
    by_contra different
    let x : Metric.sphere (0 : Space) 1 := ⟨p, Metric.mem_sphere.mpr ((dist_zero_right p).trans unit)⟩
    have interiors := (LatitudeRings.chordSphere_partition (rings_oriented positive small)).2 different
    exact (Set.disjoint_left.mp interiors) (a := x)
      (fun k => lt_of_le_of_ne (hb k) (regular b k).symm)
      (fun k => lt_of_le_of_ne (hc k) (regular c k).symm)
  subst c
  exact bi.symm.trans cj

/-- Avoiding all chord edges makes a selected chart point interior to its actual polygon. -/
theorem mem_interior_selectorSlopes_of_avoids_edges (k : Selector a) (p : Plane)
    (member : p ∈ selectorSlopes positive small k)
    (regular : ∀ (c : ChordFace a) j,
      (B c).coord j ((selectorFrame k).symm (gnomonicNormal p)) ≠ 0) :
    p ∈ interior (selectorSlopes positive small k) := by
  let direction (x : Plane) := (selectorFrame k).symm (gnomonicNormal x)
  have continuous_direction : Continuous direction :=
    (selectorFrame k).symm.continuous.comp gnomonicNormal_lipschitz.continuous
  have present : direction p ∈ selectorSphere positive small k := by
    change selectorFrame k (direction p) ∈ gnomonicNormal '' selectorSlopes positive small k
    rw [show selectorFrame k (direction p) = gnomonicNormal p from (selectorFrame k).apply_symm_apply _]
    exact ⟨p, member, rfl⟩
  obtain ⟨_, c, label, nonnegative⟩ := (mem_selectorSphere_iff positive small k _).mp present
  let U := ⋂ j : Fin 3, {x : Plane | 0 < (B c).coord j (direction x)}
  have open_U : IsOpen U := isOpen_iInter_of_finite (fun j =>
    isOpen_lt continuous_const (((B c).coord j).continuous_of_finiteDimensional.comp continuous_direction))
  have at_p : p ∈ U := Set.mem_iInter.mpr (fun j =>
    lt_of_le_of_ne (nonnegative j) (regular c j).symm)
  refine mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (open_U.mem_nhds at_p) ?_)
  intro x inside
  have unit : ‖direction x‖ = 1 := ((selectorFrame k).symm.norm_map _).trans (gnomonicNormal_unit x)
  have chosen := (mem_selectorSphere_iff positive small k _).mpr
    ⟨unit, c, label, fun j => ((Set.mem_iInter.mp inside j : 0 < (B c).coord j (direction x))).le⟩
  change selectorFrame k (direction x) ∈ gnomonicNormal '' selectorSlopes positive small k at chosen
  rw [show selectorFrame k (direction x) = gnomonicNormal x from (selectorFrame k).apply_symm_apply _]
    at chosen
  obtain ⟨y, belongs, equal⟩ := chosen
  rwa [gnomonicNormal_injective equal] at belongs

/-- A common uniform rotation avoids all actual chord edges for any finite family of directions. -/
theorem ae_avoids_selector_edge_planes {I : Type*} [Finite I] (v : I → Space)
    (unit : ∀ i, ‖v i‖ = 1) :
    ∀ᵐ g ∂SpatialRotation.probability, ∀ i (c : ChordFace a) j,
      (B c).coord j (SpatialRotation.linear g (v i)) ≠ 0 := by
  let normal (e : ChordFace a × Fin 3) := ((B e.1).coord e.2).toContinuousLinearMap
  have nonzero (e : ChordFace a × Fin 3) : normal e ≠ 0 := by
    intro zero
    have eq := congrArg (fun f : Space →L[ℝ] ℝ => f (B e.1 e.2)) zero
    change (B e.1).coord e.2 (B e.1 e.2) = 0 at eq
    rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same] at eq
    exact one_ne_zero eq
  filter_upwards [SpatialRotation.ae_avoids_finite_hyperplanes v unit normal nonzero]
    with g outside i c j
  exact outside i (c, j)

end Unfoldings.FewestNets.RevisedLatitudeGrid
