module

public import Unfoldings.FewestNets.ThreeExitAssignment
public import Unfoldings.Roof.ComponentPolygonExits

/-! Select the actual original seams and exterior rays of a three-exit component. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open FewestNets InnerProductGeometry Real Relation

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C) {slopes : Set Plane} (seed : Face)
  (B : PolygonSideDirections (Fin 3) slopes)
  (compact : IsCompact slopes) (nonempty : slopes.Nonempty)

local notation "U" => K.selectionComponent slopes seed
local notation "S" => K.restrictedCarrier U
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ S}
local notation "BVertices" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ frontier S}
local notation "retainedNonempty" => Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)
local notation "G" => K.componentClippedExtension retainedNonempty compact nonempty
local notation "p" => (fun v : V => K.projectedVertex (Subtype.val v))

/-- The chosen stems and exit continuations form a compatible routing. The side
indices are east (0), west (1), and north (2). -/
structure ThreeExitComponentRouting (δ : ℝ) where
  stems : K.ThreeExitComponentStems (slopes := slopes) seed δ
  exits : (G).ExteriorPlan BVertices
  point_eq : ∀ r, exits.point r = K.projectedVertex r.val
  direction_eq : ∀ r, exits.direction (exits.slope r) = B.normal (B.sideIndex (exits.slope r))
  outside : ∀ r t, 0 < t → exits.ray r t ∉ S
  compatible : ∀ (r : V) (hr : p r ∈ frontier S),
    let i := B.sideIndex (exits.slope ⟨r.val, hr⟩)
    (stems.choice.choosesEast r → i ≠ 1) ∧ (¬ stems.choice.choosesEast r → i ≠ 0)

open Classical in
/-- Construct the three-exit routing directly from the acute projected angle
bound and the named support sides of the slope selector. -/
theorem exists_threeExitComponentRouting {δ ε : ℝ}
    (ε_nonneg : 0 ≤ ε) (ε_lt : ε < δ) (δ_upper : δ ≤ π / 4)
    (angles : ∀ f ∈ U, ∀ i, (K.projectedTriangle f).cornerAngle i ≤ π / 2 - 2 * δ)
    (east : (exitHeadingChart false (B.normal 0)).arg ∈ Set.Icc (-ε) ε)
    (west : (exitHeadingChart true (B.normal 1)).arg ∈ Set.Icc (-ε) ε)
    (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
    (selected : K.normalSlope seed ∈ slopes) :
    Nonempty (K.ThreeExitComponentRouting seed B compact nonempty δ) := by
  let eastDir := B.normal (0 : Fin 3)
  let westDir := B.normal (1 : Fin 3)
  have dir_ne (i : Fin 3) : B.normal i ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [B.unit i]; exact one_ne_zero)
  have distinct : eastDir ≠ westDir := by
    have ε_upper : ε < π / 2 := by linarith only [ε_lt, δ_upper, pi_pos]
    have positive : 0 < eastDir 0 := threeExit_horizontal_advances false (dir_ne 0) ε_upper east
    have negative : westDir 0 < 0 :=
      neg_pos.mp (threeExit_horizontal_advances true (dir_ne 1) ε_upper west)
    intro equal
    rw [equal] at positive
    exact (lt_asymm positive negative)
  obtain ⟨P, point, direction, avoids⟩ :=
    K.exists_component_polygon_exits seed B compact nonempty no_boundary selected
  let side (r : V) (h : p r ∈ frontier S) := B.sideIndex (P.slope ⟨r.val, h⟩)
  let canEast (r : V) := ∃ h : p r ∈ frontier S, side r h ≠ 1
  let canWest (r : V) := ∃ h : p r ∈ frontier S, side r h ≠ 0
  have available (r : V) (hr : p r ∈ frontier S) : canEast r ∨ canWest r := by
    by_cases one : side r hr = 1
    · exact Or.inr ⟨hr, by rw [one]; decide⟩
    · exact Or.inl ⟨hr, one⟩
  obtain ⟨R, eqEast, eqWest⟩ :=
    K.exists_threeExitComponentStems seed (ε_nonneg.trans_lt ε_lt) angles canEast canWest available
  have point_eq (r : BVertices) : P.point r = K.projectedVertex r.val := congrFun point r
  have east_side (r : V) (hr : R.choice.forcedEast r) :
      ∃ h : p r ∈ frontier S, side r h = 0 := by
    have h : p r ∈ frontier S := R.roots_eq.subset hr.1
    refine ⟨h, ?_⟩
    have unavailable := hr.2
    rw [eqWest] at unavailable
    by_contra different
    exact unavailable ⟨h, different⟩
  have west_side (r : V) (hr : R.choice.forcedWest r) :
      ∃ h : p r ∈ frontier S, side r h = 1 := by
    have h : p r ∈ frontier S := R.roots_eq.subset hr.1
    refine ⟨h, ?_⟩
    have unavailable := hr.2
    rw [eqEast] at unavailable
    by_contra different
    exact unavailable ⟨h, different⟩
  have east_ray (r : V) (hr : p r ∈ frontier S) (he : side r hr = 0) (t : ℝ) :
      P.ray ⟨r.val, hr⟩ t = p r + t • eastDir := by
    simp only [SlopeEnvelope.ExteriorPlan.ray, point_eq, direction, eastDir]
    change p r + t • B.normal (side r hr) = p r + t • eastDir
    rw [he]
  have west_ray (r : V) (hr : p r ∈ frontier S) (hw : side r hr = 1) (t : ℝ) :
      P.ray ⟨r.val, hr⟩ t = p r + t • westDir := by
    simp only [SlopeEnvelope.ExteriorPlan.ray, point_eq, direction, westDir]
    change p r + t • B.normal (side r hr) = p r + t • westDir
    rw [hw]
  have no_path := R.no_path_of_angular_exits eastDir westDir (dir_ne 0) (dir_ne 1)
    ε_nonneg ε_lt δ_upper east west
    (fun r forced t ht => by
      obtain ⟨hr, side_eq⟩ := east_side r forced
      exact east_ray r hr side_eq t ▸ avoids ⟨r.val, hr⟩ t ht)
    (fun s forced t ht => by
      obtain ⟨hs, side_eq⟩ := west_side s forced
      exact west_ray s hs side_eq t ▸ avoids ⟨s.val, hs⟩ t ht)
    (fun r s forcedE forcedW a b ha hb equal => by
      obtain ⟨hr, er⟩ := east_side r forcedE
      obtain ⟨hs, ws⟩ := west_side s forcedW
      have opposite : P.direction (P.slope ⟨r.val, hr⟩) ≠ P.direction (P.slope ⟨s.val, hs⟩) := by
        rw [direction, direction]
        change B.normal (side r hr) ≠ B.normal (side s hs)
        rw [er, ws]
        exact distinct
      have first : p r + a • eastDir ∈ P.openRay ⟨r.val, hr⟩ :=
        ⟨a, ha, (east_ray r hr er a).symm⟩
      have last : p r + a • eastDir ∈ P.openRay ⟨s.val, hs⟩ :=
        ⟨b, hb, equal.trans (west_ray s hs ws b).symm⟩
      exact Set.disjoint_left.mp (P.open_rays_disjoint_of_direction_ne opposite) first last)
  refine ⟨⟨R, P, point_eq, direction, avoids, ?_⟩⟩
  intro r hr
  have is_root := R.roots_eq.symm.subset hr
  constructor
  · intro assigned
    have can := R.choice.eastAvailable_of_choosesEast no_path is_root assigned
    rw [eqEast] at can
    obtain ⟨_, allowed⟩ := can
    exact allowed
  · intro assigned
    have can := R.choice.westAvailable_of_not_choosesEast is_root assigned
    rw [eqWest] at can
    obtain ⟨_, allowed⟩ := can
    exact allowed

end Unfoldings.ConvexRoof
