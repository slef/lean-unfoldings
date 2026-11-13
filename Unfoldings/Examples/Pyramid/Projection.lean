module

public import Unfoldings.Examples.Pyramid.Coordinates
public import Unfoldings.Geometry.TriangleAffineEquiv
public import Unfoldings.Geometry.ConformingTriangles

/-! The four projected faces form an exact conforming partition of a convex diamond. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Examples.Pyramid

def projectedTriangle (f : Bool × Bool) : Triangle where
  vertex := ![0, vec2 (sign f.1) 0, vec2 0 (sign f.2)]
  nondegenerate := by
    obtain ⟨a, b⟩ := f
    cases a <;> cases b <;> norm_num [orient, vec2, sign]

def projection (f : Bool × Bool) : Plane ≃ᵃ[ℝ] Plane :=
  triangle.cornerEquiv (projectedTriangle f)

/-- The affine projection coordinates match the actual spatial placement. -/
theorem projection_placement (f : Bool × Bool) (x : Plane) :
    projection f x = Cap.horizontal (placement f x) := by
  have maps : (projection f).toAffineMap =
      Cap.horizontal.toAffineMap.comp (placement f).toAffineMap := by
    apply triangle.affine_ext
    intro i
    change triangle.cornerEquiv (projectedTriangle f) (triangle.vertex i) =
      Cap.horizontal (placement f (triangle.vertex i))
    rw [Triangle.cornerEquiv_vertex, placement_vertex]
    fin_cases i <;> ext j <;> fin_cases j <;> rfl
  exact congrArg (fun A : Plane →ᵃ[ℝ] Plane => A x) maps

def weight (f : Bool × Bool) (i : Fin 3) : Plane →ᵃ[ℝ] ℝ :=
  ![AffineMap.const ℝ Plane 1 -
      sign f.1 • (EuclideanSpace.proj 0).toLinearMap.toAffineMap -
      sign f.2 • (EuclideanSpace.proj 1).toLinearMap.toAffineMap,
    sign f.1 • (EuclideanSpace.proj 0).toLinearMap.toAffineMap,
    sign f.2 • (EuclideanSpace.proj 1).toLinearMap.toAffineMap] i

theorem weight_eq_coord (f : Bool × Bool) (i : Fin 3) :
    weight f i = (projectedTriangle f).coord i := by
  apply (projectedTriangle f).affine_ext
  intro j
  rw [Triangle.coord_vertex]
  obtain ⟨a, b⟩ := f
  cases a <;> cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [weight, projectedTriangle, vec2, sign]

theorem coord_apply (f : Bool × Bool) (i : Fin 3) (p : Plane) :
    (projectedTriangle f).coord i p =
      ![1 - sign f.1 * p 0 - sign f.2 * p 1, sign f.1 * p 0, sign f.2 * p 1] i := by
  rw [← weight_eq_coord]
  fin_cases i <;> rfl

theorem mem_carrier (f : Bool × Bool) (p : Plane) :
    p ∈ (projectedTriangle f).carrier ↔
      0 ≤ sign f.1 * p 0 ∧ 0 ≤ sign f.2 * p 1 ∧ sign f.1 * p 0 + sign f.2 * p 1 ≤ 1 := by
  rw [Triangle.carrier_eq_nonneg_coord]
  change (∀ i, 0 ≤ (projectedTriangle f).coord i p) ↔ _
  simp only [coord_apply, Fin.forall_fin_succ, Matrix.cons_val_zero]
  constructor
  · intro h
    exact ⟨h.2.1, h.2.2.1, by linarith [h.1]⟩
  · rintro ⟨first, last, total⟩
    exact ⟨by linarith, first, last, by simp⟩

def domain : Set Plane := {p | ∀ f : Bool × Bool, sign f.1 * p 0 + sign f.2 * p 1 ≤ 1}

theorem convex_domain : Convex ℝ domain := by
  intro x hx y hy a b ha hb sum f
  change sign f.1 * (a * x 0 + b * y 0) + sign f.2 * (a * x 1 + b * y 1) ≤ 1
  calc
    _ = a * (sign f.1 * x 0 + sign f.2 * x 1) +
        b * (sign f.1 * y 0 + sign f.2 * y 1) := by ring
    _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left (hx f) ha)
      (mul_le_mul_of_nonneg_left (hy f) hb)
    _ = 1 := by linarith

theorem projected_cover : (⋃ f, (projectedTriangle f).carrier) = domain := by
  ext p
  constructor
  · intro member
    obtain ⟨⟨a, b⟩, member⟩ := Set.mem_iUnion.mp member
    have bounds := (mem_carrier (a, b) p).mp member
    rintro ⟨c, d⟩
    cases a <;> cases b <;> cases c <;> cases d <;> simp [sign] at * <;> linarith
  · intro member
    have choose (a b : Bool) (first : 0 ≤ sign a * p 0) (last : 0 ≤ sign b * p 1) :
        p ∈ ⋃ f, (projectedTriangle f).carrier :=
      Set.mem_iUnion.mpr
        ⟨(a, b), (mem_carrier (a, b) p).mpr ⟨first, last, member (a, b)⟩⟩
    by_cases first : 0 ≤ p 0 <;> by_cases last : 0 ≤ p 1
    · exact choose false false (by simpa [sign] using first) (by simpa [sign] using last)
    · exact choose false true (by simpa [sign] using first) (by simp [sign]; linarith)
    · exact choose true false (by simp [sign]; linarith) (by simpa [sign] using last)
    · exact choose true true (by simp [sign]; linarith) (by simp [sign]; linarith)

theorem projected_separated : Pairwise (fun f g =>
    Disjoint (interior (projectedTriangle f).carrier)
      (interior (projectedTriangle g).carrier)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ different
  apply Set.disjoint_left.mpr
  intro p first last
  have first_x := ((projectedTriangle (a, b)).interior_eq_pos_coord.subset first) 1
  have first_y := ((projectedTriangle (a, b)).interior_eq_pos_coord.subset first) 2
  have last_x := ((projectedTriangle (c, d)).interior_eq_pos_coord.subset last) 1
  have last_y := ((projectedTriangle (c, d)).interior_eq_pos_coord.subset last) 2
  simp only [coord_apply] at first_x first_y last_x last_y
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [sign] <;> linarith

theorem zero_of_signs_ne {a b : Bool} (different : a ≠ b) {r : ℝ}
    (first : 0 ≤ sign a * r) (last : 0 ≤ sign b * r) : r = 0 := by
  cases a <;> cases b <;> simp_all [sign] <;> linarith

/-- Face intersections are full shared radial edges or the common apex, including endpoints. -/
theorem projected_conforming : TriangleFamily.Conforming projectedTriangle := by
  intro f g different p present
  have first := (mem_carrier f p).mp present.1
  have last := (mem_carrier g p).mp present.2
  by_cases same_x : f.1 = g.1
  · have different_y : f.2 ≠ g.2 := fun equal => different (Prod.ext same_x equal)
    have zero_y := zero_of_signs_ne different_y first.2.1 last.2.1
    refine Or.inr ⟨0, 0, ?_, ?_⟩
    · simp only [Triangle.edge, projectedTriangle, Triangle.next, Matrix.cons_val_zero,
        Matrix.cons_val_one, same_x]
    · apply ((projectedTriangle f).mem_edge_iff 0 p).mpr
      refine ⟨present.1, ?_⟩
      simp [coord_apply, zero_y, Triangle.next]
  · by_cases same_y : f.2 = g.2
    · have zero_x := zero_of_signs_ne same_x first.1 last.1
      refine Or.inr ⟨2, 2, ?_, ?_⟩
      · change segment ℝ (vec2 0 (sign f.2)) 0 = segment ℝ (vec2 0 (sign g.2)) 0
        rw [same_y]
      · apply ((projectedTriangle f).mem_edge_iff 2 p).mpr
        refine ⟨present.1, ?_⟩
        simp [coord_apply, zero_x, Triangle.next]
    · have zero_x := zero_of_signs_ne same_x first.1 last.1
      have zero_y := zero_of_signs_ne same_y first.2.1 last.2.1
      have zero : p = 0 := by ext i; fin_cases i <;> assumption
      subst p
      exact Or.inl ⟨⟨0, rfl⟩, ⟨0, rfl⟩⟩

end Unfoldings.Examples.Pyramid
