module

public import Unfoldings.Polyhedron.NonextremeCreases
public import Unfoldings.Polyhedron.LinkDirections
public import Unfoldings.Geometry.UnitLine

/-!
# At most two genuine creases occur in a nonextreme vertex link

All crease rays lie along the derived common axis. Equal unit directions
identify actual seam mates, so the initial germs of a cyclic chain see each
axis ray at most once. This counts genuine plane changes; coplanar triangle
subdivisions are retained.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem nonextreme_crease_count_le_two (v : C.Vertex Set.univ)
    (not_extreme : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∉ F.vertexHull.extremePoints ℝ)
    {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first) :
    Fintype.card {i : Fin (n + 1) //
      LinearMap.range (F.place (c.point i).val.1.1).linear ≠
        LinearMap.range (F.place (C.linkMate Set.univ v (c.point i)).val.1.1).linear} ≤ 2 := by
  classical
  obtain ⟨d, nonzero, axis⟩ := P.exists_nonextreme_crease_axis v not_extreme
  let S := {i : Fin (n + 1) //
    LinearMap.range (F.place (c.point i).val.1.1).linear ≠
      LinearMap.range (F.place (C.linkMate Set.univ v (c.point i)).val.1.1).linear}
  let direction (i : S) := F.germUnitDirection (c.point i.val).val
  let u := ‖d‖⁻¹ • d
  have signs (i : S) : direction i = u ∨ direction i = -u :=
    inv_norm_smul_eq_or_eq_neg_of_mem_span nonzero (F.germDirection_ne_zero _)
      (axis (c.point i.val) i.property)
  have injective : Function.Injective direction :=
    (F.linkDirection_chain_injective P.embedded c closes).comp Subtype.val_injective
  have included : Finset.univ.image direction ⊆ ({u, -u} : Finset Space) := by
    intro z hz
    obtain ⟨i, _member, rfl⟩ := Finset.mem_image.mp hz
    simpa only [Finset.mem_insert, Finset.mem_singleton] using signs i
  calc
    Fintype.card S = (Finset.univ.image direction).card := by
      rw [Finset.card_image_of_injective _ injective, Finset.card_univ]
    _ ≤ ({u, -u} : Finset Space).card := Finset.card_le_card included
    _ ≤ 2 := Finset.card_le_two

end Unfoldings.SpatialFolding.ConvexBoundary
