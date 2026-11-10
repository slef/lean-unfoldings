module

public import Unfoldings.Geometry.MeshProgress
public import Unfoldings.Geometry.Shear

/-!
# Outgoing edges in strict acute wedges

A small positive shear makes the pullback of a strict quadrant narrower than
pi/2. The shear size can be chosen from the acute margin alone. Mesh progress
then supplies original edges in this narrower direction wedge.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

def quadrantShearHomeomorph (t : ℝ) : Plane ≃ₜ Plane where
  toFun := quadrantShear t
  invFun := quadrantShear (-t)
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp
  continuous_toFun := (quadrantShear t).continuous_of_finiteDimensional
  continuous_invFun := (quadrantShear (-t)).continuous_of_finiteDimensional

theorem quadrantShear_affine_injective (t : ℝ) :
    Function.Injective (quadrantShear t).toAffineMap := quadrantShear_injective t

namespace Triangle

def sheared (T : Triangle) (t : ℝ) : Triangle :=
  T.affineImage (quadrantShear t).toAffineMap (quadrantShear_affine_injective t)

@[simp] theorem sheared_vertex (T : Triangle) (t : ℝ) (i : Fin 3) :
    (T.sheared t).vertex i = quadrantShear t (T.vertex i) := rfl

theorem sheared_cornerAngle (T : Triangle) (t : ℝ) (i : Fin 3) :
    (T.sheared t).cornerAngle i =
      InnerProductGeometry.angle
        (quadrantShear t (T.vertex (next i) - T.vertex i))
        (quadrantShear t (T.vertex (next (next i)) - T.vertex i)) := by
  change InnerProductGeometry.angle
    (quadrantShear t (T.vertex (next i)) - quadrantShear t (T.vertex i))
    (quadrantShear t (T.vertex (next (next i))) - quadrantShear t (T.vertex i)) = _
  rw [← map_sub, ← map_sub]

end Triangle

/-- The same positive shear makes every triangle with the prescribed acute margin acute. -/
theorem exists_shear_acute_triangles {α : ℝ} (positive : 0 < α) (small : α < Real.pi / 2) :
    ∃ t > 0, ∀ T : Triangle, (∀ i, T.cornerAngle i ≤ Real.pi / 2 - α) →
      ∀ i, (T.sheared t).cornerAngle i < Real.pi / 2 := by
  obtain ⟨t, tpos, bound⟩ := exists_acute_quadrantShear positive small
  refine ⟨t, tpos, fun T acute i => ?_⟩
  rw [T.sheared_cornerAngle]
  apply lt_of_not_ge
  intro nonacute
  have nonpositive := InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mpr nonacute
  have first : T.vertex (Triangle.next i) - T.vertex i ≠ 0 := sub_ne_zero.mpr
    (T.affineIndependent_vertices.injective.ne (by fin_cases i <;> decide))
  have last : T.vertex (Triangle.next (Triangle.next i)) - T.vertex i ≠ 0 := sub_ne_zero.mpr
    (T.affineIndependent_vertices.injective.ne (by fin_cases i <;> decide))
  exact (not_lt_of_ge nonpositive) (bound _ _ first last (acute i))

/-- Local mesh progress pulled back through the shear uses the original triangle edges. -/
theorem exists_mesh_sheared_quadrant_edge {Face : Type*} [Finite Face]
    (triangle : Face → Triangle) (t : ℝ) (region : Set Plane)
    (cover : region ⊆ ⋃ f, (triangle f).carrier) (center : Plane)
    (inside : center ∈ interior region)
    (corner : ∀ f, center ∈ (triangle f).carrier → ∃ i, (triangle f).vertex i = center)
    (acute : ∀ f i, ((triangle f).sheared t).cornerAngle i < Real.pi / 2) :
    ∃ f i, (triangle f).vertex i = center ∧
      (StrictQuadrant (quadrantShear t ((triangle f).vertex (Triangle.next i) - center)) ∨
      StrictQuadrant (quadrantShear t
        ((triangle f).vertex (Triangle.next (Triangle.next i)) - center))) := by
  let A := quadrantShearHomeomorph t
  let moved : Face → Triangle := fun f => (triangle f).sheared t
  have cover_moved : A '' region ⊆ ⋃ f, (moved f).carrier := by
    rintro _ ⟨p, present, rfl⟩
    obtain ⟨f, carrier⟩ := Set.mem_iUnion.mp (cover present)
    apply Set.mem_iUnion.mpr
    refine ⟨f, ?_⟩
    change quadrantShear t p ∈ ((triangle f).sheared t).carrier
    rw [Triangle.sheared, Triangle.affineImage_carrier]
    exact ⟨p, carrier, rfl⟩
  have center_inside : A center ∈ interior (A '' region) := by
    rw [← A.image_interior]
    exact Set.mem_image_of_mem A inside
  have moved_corner (f : Face) (present : A center ∈ (moved f).carrier) :
      ∃ i, (moved f).vertex i = A center := by
    change quadrantShear t center ∈ ((triangle f).sheared t).carrier at present
    rw [Triangle.sheared, Triangle.affineImage_carrier] at present
    obtain ⟨p, carrier, image⟩ := present
    have same : p = center := A.injective image
    obtain ⟨i, vertex⟩ := corner f (same ▸ carrier)
    exact ⟨i, congrArg A vertex⟩
  obtain ⟨f, i, vertex, progress⟩ := exists_mesh_quadrant_edge moved (A '' region) cover_moved
    (A center) center_inside moved_corner acute
  refine ⟨f, i, A.injective vertex, ?_⟩
  change StrictQuadrant (quadrantShear t ((triangle f).vertex (Triangle.next i)) -
      quadrantShear t center) ∨
    StrictQuadrant (quadrantShear t ((triangle f).vertex (Triangle.next (Triangle.next i))) -
      quadrantShear t center) at progress
  simpa only [map_sub] using progress

end Unfoldings
