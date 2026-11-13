module

public import Unfoldings.Examples.Pyramid.Embedding
public import Unfoldings.Examples.Pyramid.Normals
public import Unfoldings.Cap.Basic

/-!
# A genuine nonflat convex cap

The cap has four equilateral faces, apex `(0,0,1)`, and rim vertices
`(1,0,0)`, `(0,1,0)`, `(-1,0,0)`, `(0,-1,0)`. Its vertical projection
is exactly the closed diamond, with all point identifications proved from
its four actual radial seams. No abstract cap hypothesis is postulated.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.Examples.Pyramid

theorem projected_surface : Cap.horizontal '' folding.surface = domain := by
  have each (f : Bool × Bool) : Cap.horizontal '' (placement f '' triangle.carrier) =
      (projectedTriangle f).carrier := by
    rw [Set.image_image]
    have functions : (fun x => Cap.horizontal (placement f x)) = projection f :=
      (funext (projection_placement f)).symm
    rw [functions]
    calc
      _ = (complex.affineProjectedTriangle projection f).carrier :=
        (triangle.affineImage_carrier (projection f).toAffineMap (projection f).injective).symm
      _ = _ := congrArg (fun family => (family f).carrier) projected_family
  change Cap.horizontal '' (⋃ f, placement f '' triangle.carrier) = domain
  rw [Set.image_iUnion]
  simp_rw [each]
  exact projected_cover

theorem boundary_edge_iff (f : Bool × Bool) (e : Fin 3) :
    complex.IsBoundaryEdge Set.univ ⟨f, e⟩ ↔ e = 1 := by
  change (¬ ∃ s : Bool × Bool, s ∈ (Set.univ : Set (Bool × Bool)) ∧
    ((⟨f, e⟩ : EdgeRef (Bool × Bool)) = left s ∨
      (⟨f, e⟩ : EdgeRef (Bool × Bool)) = right s)) ↔ e = 1
  simp only [Set.mem_univ, true_and]
  obtain ⟨a, b⟩ := f
  cases a <;> cases b <;> fin_cases e <;> decide

def cap : ConvexCap complex where
  folding := folding
  normal := normal
  normal_unit := normal_unit
  normal_upward := normal_upward
  normal_tangent := normal_tangent
  supporting := supporting
  projection_injective := projection_injective
  convex_projection := by rw [projected_surface]; exact convex_domain
  interior_projection := by
    rw [projected_surface, ← projected_cover]
    exact (projectedTriangle (false, false)).interior_nonempty.mono
      (interior_mono (Set.subset_iUnion (fun f => (projectedTriangle f).carrier) (false, false)))
  rim_horizontal := by
    intro bank x
    have edge : bank.val.edge = 1 :=
      (boundary_edge_iff bank.val.face bank.val.edge).mp bank.property
    have point : x.val ∈ triangle.edge 1 := edge ▸ x.property
    have zero := triangle.coord_edge_eq_zero 1 ⟨x.val, point⟩
    change placement bank.val.face x.val 2 = 0
    rw [placement_coordinates]
    exact zero
  corners_above := by
    intro f i
    change 0 ≤ placement f (triangle.vertex i) 2
    rw [placement_vertex]
    fin_cases i <;> simp [vertex, vec3]

/-- The apex has positive height, so this is a genuine cap rather than a planar disk. -/
theorem apex_height : folding.place (false, false) (triangle.vertex 0) 2 = 1 := by
  change placement (false, false) (triangle.vertex 0) 2 = 1
  rw [placement_vertex]
  rfl

/-- The four faces have nonvertical normals; the flat-cap hypothesis fails. -/
theorem not_flat : ¬ cap.TiltBound 0 := by
  intro flat
  have bound := flat (false, false)
  change Real.cos 0 ≤ (Real.sqrt 3)⁻¹ * 1 at bound
  rw [Real.cos_zero, mul_one] at bound
  have root : 1 < Real.sqrt 3 := by
    have square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have inverse : (Real.sqrt 3)⁻¹ < 1 := inv_lt_one_of_one_lt₀ root
  exact not_lt_of_ge bound inverse

/-- Every triangle of this genuine nonflat example is strictly acute. -/
theorem corner_acute (i : Fin 3) : triangle.cornerAngle i < Real.pi / 2 := by
  have mapped := basePlacement.angle_map (triangle.vertex (Triangle.next i))
    (triangle.vertex i) (triangle.vertex (Triangle.next (Triangle.next i)))
  change EuclideanGeometry.angle _ _ _ = triangle.cornerAngle i at mapped
  rw [← mapped]
  change InnerProductGeometry.angle
    (basePlacement (triangle.vertex (Triangle.next i)) - basePlacement (triangle.vertex i))
    (basePlacement (triangle.vertex (Triangle.next (Triangle.next i))) -
      basePlacement (triangle.vertex i)) < Real.pi / 2
  rw [basePlacement_vertex, basePlacement_vertex, basePlacement_vertex]
  apply lt_of_not_ge
  intro obtuse
  have nonpositive := InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mpr obtuse
  fin_cases i <;>
    norm_num [Triangle.next, vec3, PiLp.inner_apply, Fin.sum_univ_three] at nonpositive

/-- The example supplies a common positive spatial acute margin, rather than assuming one. -/
theorem exists_acute_margin : ∃ α > 0, ConvexCap.AcuteMargin (C := complex) α := by
  let gap := min (Real.pi / 2 - triangle.cornerAngle 0)
    (min (Real.pi / 2 - triangle.cornerAngle 1) (Real.pi / 2 - triangle.cornerAngle 2))
  have positive : 0 < gap := lt_min (sub_pos.mpr (corner_acute 0))
    (lt_min (sub_pos.mpr (corner_acute 1)) (sub_pos.mpr (corner_acute 2)))
  refine ⟨gap / 2, half_pos positive, ?_⟩
  intro f i
  change triangle.cornerAngle i ≤ Real.pi / 2 - gap / 2
  have first : gap ≤ Real.pi / 2 - triangle.cornerAngle 0 := min_le_left _ _
  have middle : gap ≤ Real.pi / 2 - triangle.cornerAngle 1 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have last : gap ≤ Real.pi / 2 - triangle.cornerAngle 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  fin_cases i
  · change triangle.cornerAngle 0 ≤ Real.pi / 2 - gap / 2
    linarith only [first, positive]
  · change triangle.cornerAngle 1 ≤ Real.pi / 2 - gap / 2
    linarith only [middle, positive]
  · change triangle.cornerAngle 2 ≤ Real.pi / 2 - gap / 2
    linarith only [last, positive]

end Unfoldings.Examples.Pyramid
