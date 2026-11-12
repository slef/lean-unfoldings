module

public import Unfoldings.Cap.SectorBoundaryCutPoints
public import Unfoldings.Geometry.RadialTailPositions

/-! A skirt component on a sector boundary has no original tree attached to it. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  (positive : 0 < t) (small : t < 1)

include positive small

/-- Every nontrivial original tree reaches the rim strictly inside its
assigned sector, even when its first leaf is on a boundary ray. -/
theorem root_position_strict_of_nonroot
    (e : {w : C.Vertex Set.univ // w ∉ M.parents.roots}) :
    K.projectedVertex (M.parents.root e.val) - K.projectedVertex origin ∈
      strictFiveSector t (Sum.inl (K.sourceSectorLabel t origin e.val)) := by
  have distance : 0 < M.parents.distanceToRoot e.val := Nat.pos_of_ne_zero
    (fun zero => e.property ((M.parents.distanceToRoot_eq_zero_iff e.val).mp zero))
  let k := M.parents.distanceToRoot e.val - 1
  have before : k < M.parents.distanceToRoot e.val := by dsimp only [k]; omega
  have next : k + 1 = M.parents.distanceToRoot e.val := by dsimp only [k]; omega
  let last : {w : C.Vertex Set.univ // w ∉ M.parents.roots} :=
    ⟨M.parents.parent^[k] e.val, M.parents.iterate_lt_distanceToRoot_not_mem e.val before⟩
  have at_root : M.parents.parent last.val = M.parents.root e.val := by
    change M.parents.parent (M.parents.parent^[k] e.val) = _
    rw [← Function.iterate_succ_apply' M.parents.parent k e.val]
    change M.parents.parent^[k + 1] e.val = _
    rw [next, M.parents.iterate_distanceToRoot_eq_root]
  have strict := M.original_parent_point_strict_or_start positive small last
    (right_mem_segment ℝ (K.projectedVertex last.val)
      (K.projectedVertex (M.parents.parent last.val)))
  have actual := strict.resolve_left (Ne.symm (M.projected_parent_ne last))
  rw [at_root] at actual
  have label := M.iterate_label positive.le small e.val k
  change K.sourceSectorLabel t origin last.val = K.sourceSectorLabel t origin e.val at label
  rwa [label] at actual

variable {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (lower : Z < 0)

/-- A component touching any sector boundary is purely radial: an attached
original edge would put its whole radial skirt strictly inside one sector. -/
theorem sector_boundary_component_unattached {c : F.Component} {x : Plane}
    (member : x ∈ (F.componentTail c).carrier)
    (boundary : ∀ i, x - K.projectedVertex origin ∉ strictFiveSector t i) :
    ∀ e : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
      M.cutPieceLabel F covered (Sum.inl e) ≠ c := by
  intro e equal
  have root_member : K.projectedVertex (M.parents.root e.val) ∈ (F.componentTail c).carrier :=
    (congrArg (fun d => (F.componentTail d).carrier) equal).subset
      (F.rimComponent_mem covered _ (M.rootPath_end_boundary e.val))
  obtain ⟨a, apos, scale⟩ :=
    (F.componentTail c).exists_pos_smul_sub_eq_of_members root_member member
  have strict := M.root_position_strict_of_nonroot positive small e
  apply boundary (Sum.inl (K.sourceSectorLabel t origin e.val))
  change 0 < fiveSectorCoordinates t (Sum.inl (K.sourceSectorLabel t origin e.val))
      (x - K.projectedVertex origin) 0 ∧
    0 < fiveSectorCoordinates t (Sum.inl (K.sourceSectorLabel t origin e.val))
      (x - K.projectedVertex origin) 1
  rw [scale, map_smul]
  exact ⟨mul_pos apos strict.1, mul_pos apos strict.2⟩

/-- A pure radial component can use any sector containing its ray. This
allows the same actual component to be compared from both neighboring sectors. -/
def radialComponentSector (c : F.Component)
    (unattached : ∀ e : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
      M.cutPieceLabel F covered (Sum.inl e) ≠ c)
    {x : Plane} (member : x ∈ (F.componentTail c).carrier)
    (i : FiveSector) (inside : x - K.projectedVertex origin ∈ closedFiveSector t i) :
    M.GeometricComponentSector F covered positive small lower c where
  sector := i
  positions w component := by
    have radial_positions : ∀ y ∈ (F.componentTail c).carrier,
        y - K.projectedVertex origin ∈ closedFiveSector t i :=
      fun _ last => (F.componentTail c).position_inDirectionWedge_of_mem member inside last
    cases w with
    | inl w =>
      by_cases boundary : C.IsBoundaryVertex Set.univ w
      · have label := (M.geometricComponent_rim F covered w boundary).symm.trans component
        exact radial_positions _
          ((congrArg (fun d => (F.componentTail d).carrier) label).subset
            (F.rimComponent_mem covered w boundary))
      · have nonroot : w ∉ M.parents.roots := by
          simpa only [M.roots_eq, Set.mem_ofPred_eq] using boundary
        exact (unattached ⟨w, nonroot⟩ component).elim
    | inr w =>
      cases w with
      | inl d =>
        change d.val = c at component
        change F.componentSeed d.val - K.projectedVertex origin ∈ _
        rw [component]
        exact radial_positions _ (F.componentTail c).seed_mem
      | inr d =>
        change d = c at component
        subst d
        exact radial_positions _ (F.componentTail c).tip_mem
  directions w nonroot component := by
    obtain ⟨piece, first, last, label⟩ := M.geometric_parent_piece F covered positive small lower
      w nonroot
    cases piece with
    | inl e => exact (unattached e (label.trans component)).elim
    | inr d =>
      have same : d = c := label.trans component
      subst d
      obtain ⟨a, nonnegative, direction⟩ :=
        (F.componentTail c).direction_eq_nonneg_smul_of_mem member
      rw [← last, ← first]
      change (F.componentTail c).tip - F.componentSeed c ∈ closedFiveSector t i
      change (F.componentTail c).tip - F.componentSeed c = _ at direction
      rw [direction]
      exact inside.nonneg_smul nonnegative

end Unfoldings.ConvexCap.SectorForest
