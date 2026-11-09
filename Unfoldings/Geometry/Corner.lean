module

public import Unfoldings.Geometry.Barycentric

/-! Actual supporting wedges and radial geometry at triangle corners. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

@[simp] theorem next_next_next (i : Fin 3) : next (next (next i)) = i := by
  fin_cases i <;> rfl

/-- The infinite supporting wedge of the two edges incident to a corner. -/
def cornerWedge (T : Triangle) (i : Fin 3) : Set Plane :=
  {p | 0 ≤ T.coord (next i) p ∧ 0 ≤ T.coord (next (next i)) p}

theorem convex_cornerWedge (T : Triangle) (i : Fin 3) : Convex ℝ (T.cornerWedge i) :=
  ((convex_Ici (0 : ℝ)).affine_preimage (T.coord (next i))).inter
    ((convex_Ici (0 : ℝ)).affine_preimage (T.coord (next (next i))))

theorem isClosed_cornerWedge (T : Triangle) (i : Fin 3) : IsClosed (T.cornerWedge i) :=
  (isClosed_le continuous_const (T.continuous_coord (next i))).inter
    (isClosed_le continuous_const (T.continuous_coord (next (next i))))

theorem carrier_subset_cornerWedge (T : Triangle) (i : Fin 3) : T.carrier ⊆ T.cornerWedge i := by
  intro p inside
  have coordinates := T.carrier_eq_nonneg_coord.le inside
  exact ⟨coordinates _, coordinates _⟩

theorem vertex_mem_cornerWedge (T : Triangle) (i : Fin 3) : T.vertex i ∈ T.cornerWedge i :=
  T.carrier_subset_cornerWedge i (T.vertex_mem i)

theorem mem_carrier_iff_of_corner_coord_pos (T : Triangle) (i : Fin 3) (p : Plane)
    (positive : 0 < T.coord i p) : p ∈ T.carrier ↔ p ∈ T.cornerWedge i := by
  constructor
  · exact fun h => T.carrier_subset_cornerWedge i h
  · intro wedge
    apply T.carrier_eq_nonneg_coord.ge
    intro j
    rcases corner_cases i j with rfl | rfl | rfl
    · exact positive.le
    · exact wedge.1
    · exact wedge.2

/-- Near a corner, the bounded triangle is exactly its infinite supporting wedge. -/
theorem exists_ball_cornerWedge (T : Triangle) (i : Fin 3) : ∃ r > 0,
    ∀ p ∈ Metric.ball (T.vertex i) r, p ∈ T.carrier ↔ p ∈ T.cornerWedge i := by
  have open_set : IsOpen {p : Plane | 0 < T.coord i p} :=
    isOpen_lt continuous_const (T.continuous_coord i)
  obtain ⟨r, positive, ball⟩ := Metric.isOpen_iff.mp open_set (T.vertex i) (by simp)
  exact ⟨r, positive, fun p hp => T.mem_carrier_iff_of_corner_coord_pos i p (ball hp)⟩

/-- There is positive clearance from the corner to its opposite edge. -/
theorem exists_radius_clear_opposite_edge (T : Triangle) (i : Fin 3) : ∃ r > 0,
    ∀ p ∈ T.edge (next i), r ≤ dist p (T.vertex i) := by
  have open_set : IsOpen {p : Plane | 0 < T.coord i p} :=
    isOpen_lt continuous_const (T.continuous_coord i)
  obtain ⟨r, positive, ball⟩ := Metric.isOpen_iff.mp open_set (T.vertex i) (by simp)
  refine ⟨r, positive, ?_⟩
  intro p inside
  by_contra close
  have positive_coord := ball (Metric.mem_ball.mpr (lt_of_not_ge close))
  have zero : T.coord i p = 0 := by
    simpa only [next_next_next] using T.coord_edge_eq_zero (next i) ⟨p, inside⟩
  exact (ne_of_gt positive_coord) zero

/-- The wedge is invariant under nonnegative radial scaling about its corner. -/
theorem lineMap_mem_cornerWedge (T : Triangle) (i : Fin 3) {p : Plane}
    (inside : p ∈ T.cornerWedge i) {t : ℝ} (nonnegative : 0 ≤ t) :
    AffineMap.lineMap (T.vertex i) p t ∈ T.cornerWedge i := by
  have next_ne : next i ≠ i := by fin_cases i <;> decide
  have prev_ne : next (next i) ≠ i := by fin_cases i <;> decide
  constructor
  · rw [(T.coord (next i)).apply_lineMap]
    simpa only [T.coord_vertex, ite_eq_right next_ne, AffineMap.lineMap_apply_ring,
      mul_zero, sub_zero, zero_add] using mul_nonneg nonnegative inside.1
  · rw [(T.coord (next (next i))).apply_lineMap]
    simpa only [T.coord_vertex, ite_eq_right prev_ne, AffineMap.lineMap_apply_ring,
      mul_zero, sub_zero, zero_add] using mul_nonneg nonnegative inside.2

/-- A wedge ball, before identifying its radial banks with neighboring corner pieces. -/
def cornerBall (T : Triangle) (i : Fin 3) (r : ℝ) : Set Plane :=
  Metric.ball (T.vertex i) r ∩ T.cornerWedge i

/-- The planar wedge ball is exactly the original triangle-cell ball at small radii. -/
def cornerBallIsometry (T : Triangle) (i : Fin 3) (r : ℝ)
    (wedge : ∀ p ∈ Metric.ball (T.vertex i) r, p ∈ T.carrier ↔ p ∈ T.cornerWedge i) :
    T.cornerBall i r ≃ᵢ Metric.ball (⟨T.vertex i, T.vertex_mem i⟩ : T.Cell) r where
  toEquiv :=
    { toFun := fun p => ⟨⟨p.val, (wedge p.val p.property.1).mpr p.property.2⟩,
        Metric.mem_ball.mpr (Metric.mem_ball.mp p.property.1)⟩
      invFun := fun p => ⟨p.val.val, by
        have near : p.val.val ∈ Metric.ball (T.vertex i) r :=
          Metric.mem_ball.mpr (Metric.mem_ball.mp p.property)
        exact ⟨near, (wedge p.val.val near).mp p.val.property⟩⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext (Subtype.ext rfl) }
  isometry_toFun := fun _ _ => rfl

end Unfoldings.Triangle
