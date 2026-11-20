module

public import Unfoldings.Polyhedron.NonextremeCreaseCount
public import Unfoldings.Polyhedron.NonextremePlanes
public import Unfoldings.Polyhedron.FaceNormalContact
public import Unfoldings.Polyhedron.GaussianVertexAngles
public import Unfoldings.Combinatorics.ComponentEulerAccounting

/-! Nonextreme triangulation vertices have zero component-count charge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

include P in
/-- Two supported faces in the same plane have the same outward unit normal. -/
theorem normal_eq_of_tangent_range_eq_of_shared_point (f g : Face) (x y : Plane)
    (shared : F.place f x = F.place g y)
    (planes : LinearMap.range (F.place f).linear = LinearMap.range (F.place g).linear) :
    N.normal f = N.normal g := by
  have tangent (p : Plane) : inner ℝ (N.normal g) ((F.place f).linear p) = 0 := by
    have member : (F.place f).linear p ∈ LinearMap.range (F.place g).linear :=
      planes ▸ LinearMap.mem_range_self _ p
    obtain ⟨q, same⟩ := LinearMap.mem_range.mp member
    rw [← same, N.tangent g]
  obtain ⟨z, inside⟩ := P.interior_nonempty
  apply unit_normal_unique (F.place f) _ _ (N.unit f) (N.unit g) (N.tangent f) tangent z
    (N.supporting_strict f inside)
  have chord := (F.place f).toAffineMap.linear_apply_vsub x 0
  change (F.place f).linear (x - 0) = F.place f x - F.place f 0 at chord
  have on_f := tangent (x - 0)
  rw [chord, shared] at on_f
  have on_g := N.on_plane g y
  have strict := N.supporting_strict g inside
  rw [inner_sub_right] at on_f on_g strict ⊢
  linarith only [on_f, on_g, strict]

include P in
/-- Normal labels at the incoming germ and the previous corner agree in every
closed original vertex link, including flat subdivisions. -/
theorem linkNormal_mate_eq_prev {v : C.Vertex Set.univ} {n : ℕ}
    (c : (C.linkSystem Set.univ v).Chain n)
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) :
    N.normal (C.linkMate Set.univ v (c.point i)).val.1.1 =
      N.normal (c.point ((finRotate (n + 1)).symm i)).val.1.1 := by
  let a := C.linkMate Set.univ v (c.point i)
  let b := c.point ((finRotate (n + 1)).symm i)
  have at_a := F.toSpace_vertexOfCorner a.val.1.1 a.val.1.2
  have at_b := F.toSpace_vertexOfCorner b.val.1.1 b.val.1.2
  rw [a.property] at at_a
  rw [b.property] at at_b
  exact P.normal_eq_of_tangent_range_eq_of_shared_point N _ _ _ _ (at_a.symm.trans at_b)
    (F.linkPlane_mate_eq_prev c closes i)

open Classical in
include P in
/-- Flat or crease subdivision vertices contribute zero to the component charge.
A normal-dependent labeling changes at most twice on their cyclic links. -/
theorem componentCharge_eq_zero_of_nonextreme_link {L : Type*} (label : Space → L)
    (v : C.Vertex Set.univ)
    (not_extreme : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∉ F.vertexHull.extremePoints ℝ)
    {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first) :
    componentCharge ((Finset.univ : Finset (Fin (n + 1))).filter
      (fun i => label (N.normal (c.point i).val.1.1) ≠
        label (N.normal (C.linkMate Set.univ v (c.point i)).val.1.1))).card = 0 := by
  classical
  let labels (i : Fin (n + 1)) := label (N.normal (c.point i).val.1.1)
  let next := (finRotate (n + 1)).symm
  have before (i : Fin (n + 1)) :
      N.normal (C.linkMate Set.univ v (c.point i)).val.1.1 =
        N.normal (c.point (next i)).val.1.1 := P.linkNormal_mate_eq_prev N c closes i
  simp only [before]
  change componentCharge (Finset.univ.filter fun i => labels i ≠ labels (next i)).card = 0
  have one := card_label_changes_ne_one next labels
  let changed := (Finset.univ : Finset (Fin (n + 1))).filter
    (fun i => labels i ≠ labels (next i))
  have bounded : changed.card ≤ 2 := by
    let crease := (Finset.univ : Finset (Fin (n + 1))).filter (fun i =>
      LinearMap.range (F.place (c.point i).val.1.1).linear ≠
        LinearMap.range (F.place (C.linkMate Set.univ v (c.point i)).val.1.1).linear)
    have included : changed ⊆ crease := by
      intro i hi
      have different := (Finset.mem_filter.mp hi).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro same
      let a := c.point i
      let b := C.linkMate Set.univ v a
      have at_a := F.toSpace_vertexOfCorner a.val.1.1 a.val.1.2
      have at_b := F.toSpace_vertexOfCorner b.val.1.1 b.val.1.2
      rw [a.property] at at_a
      rw [b.property] at at_b
      have normals := P.normal_eq_of_tangent_range_eq_of_shared_point N _ _ _ _
        (at_a.symm.trans at_b) same
      apply different
      change label (N.normal a.val.1.1) = label (N.normal (c.point (next i)).val.1.1)
      rw [normals]
      exact congrArg label (before i)
    have at_most := P.nonextreme_crease_count_le_two v not_extreme c closes
    have crease_card : crease.card ≤ 2 := by
      simpa only [crease, Fintype.card_subtype] using at_most
    exact (Finset.card_le_card included).trans crease_card
  change changed.card ≠ 1 at one
  change componentCharge changed.card = 0
  have values : changed.card = 0 ∨ changed.card = 2 := by omega
  rcases values with h | h <;> norm_num [h, componentCharge]

end Unfoldings.SpatialFolding.ConvexBoundary
