module

public import Unfoldings.FewestNets.CheckedVisualSide
public import Unfoldings.Geometry.PlanarWedgeAngle
public import Unfoldings.Geometry.ConeBoundaryRays
public import Unfoldings.Geometry.CyclicConvexVertices

/-! Whole-panel upper visual angles from one enclosing wedge and linear endpoint tests. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry Real

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

variable {D m : ℕ} (hD : 0 < D) {u v a b : Plane} {body : Fin m → Plane}
  (cu : CheckedPlane D u) (cv : CheckedPlane D v)
  (ca : CheckedPlane D a) (cb : CheckedPlane D b)
  (vertices : ∀ i, CheckedPlane D (body i))

/-- Check a common viewing wedge at the two endpoints of a whole panel.
The number of tests is linear in the number of body vertices. -/
def checkUpperVisualPanel {c : ℝ} (coeff : CheckedReal D c) : Bool :=
  let cross := CheckedPlane.det hD cu cv
  cross.isPositive && ((CheckedPlane.dot hD cu cv).add (coeff.mul hD cross)).isPositive &&
    (List.finRange m).all fun i =>
      let first := CheckedPlane.sub ca (vertices i)
      let last := CheckedPlane.sub cb (vertices i)
      (CheckedPlane.det hD cu first).isPositive && (CheckedPlane.det hD first cv).isPositive &&
        (CheckedPlane.det hD cu last).isPositive && (CheckedPlane.det hD last cv).isPositive

private theorem mem_strictRayCone_of_positive_orient {u x v : Plane}
    (uv : 0 < orient 0 u v) (ux : 0 < orient 0 u x) (xv : 0 < orient 0 x v) :
    x ∈ strictRayCone u v := by
  refine ⟨orient 0 x v / orient 0 u v, div_pos xv uv,
    orient 0 u x / orient 0 u v, div_pos ux uv, ?_⟩
  have h := congrArg (fun w : Plane => (orient 0 u v)⁻¹ • w) (orient_zero_balance u x v)
  simpa only [smul_add, smul_smul, div_eq_inv_mul, inv_mul_cancel₀ uv.ne', one_smul] using h

private theorem strictRayCone_lineMap {u v x y : Plane}
    (first : x ∈ strictRayCone u v) (last : y ∈ strictRayCone u v)
    {t : ℝ} (bounds : t ∈ Set.Icc 0 1) :
    AffineMap.lineMap x y t ∈ strictRayCone u v := by
  obtain ⟨a, ap, b, bp, rfl⟩ := first
  obtain ⟨c, cp, d, dp, rfl⟩ := last
  refine ⟨(1 - t) * a + t * c, ?_, (1 - t) * b + t * d, ?_, ?_⟩
  · rcases eq_or_lt_of_le bounds.1 with zero | pos
    · simpa only [← zero, sub_zero, one_mul, zero_mul, add_zero] using ap
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr bounds.2) ap.le) (mul_pos pos cp)
  · rcases eq_or_lt_of_le bounds.1 with zero | pos
    · simpa only [← zero, sub_zero, one_mul, zero_mul, add_zero] using bp
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr bounds.2) bp.le) (mul_pos pos dp)
  · rw [AffineMap.lineMap_apply_module']
    module

private theorem strictRayCone_subset_directionWedge {u v : Plane} :
    strictRayCone u v ⊆ {x | InDirectionWedge u v x} := by
  rintro _ ⟨a, ap, b, bp, eq⟩
  exact ⟨a, b, ap.le, bp.le, eq⟩

/-- A successful panel test bounds the visual angle of every pair of body
vertices at every point of the panel, even where the extreme pair changes. -/
theorem upperVisualAngle_of_checked_panel {c α : ℝ} (coeff : CheckedReal D c)
    (positive : 0 < α) (small : α ≤ π / 2) (c_nonnegative : 0 ≤ c)
    (cotangent : c * sin α < cos α)
    (passed : checkUpperVisualPanel hD cu cv ca cb vertices coeff = true)
    {t : ℝ} (bounds : t ∈ Set.Icc 0 1) (i j : Fin m) :
    angle (AffineMap.lineMap a b t - body i) (AffineMap.lineMap a b t - body j) < π - α := by
  unfold checkUpperVisualPanel at passed
  dsimp only at passed
  simp only [Bool.and_eq_true] at passed
  have det_pos : 0 < orient 0 u v := by
    simpa only [orient, PiLp.zero_apply, sub_zero] using
      CheckedReal.positive_of_isPositive hD _ passed.1.1
  have c_positive : 0 < inner ℝ u v + c * |certificateOrientation.areaForm u v| := by
    have h := CheckedReal.positive_of_isPositive hD _ passed.1.2
    rw [areaForm_certificateOrientation, abs_of_pos]
    · exact h
    · simpa only [orient, PiLp.zero_apply, sub_zero] using det_pos
  have upper : angle u v < π - α := by
    have h := visualAngle_lt_supplement_of_outside_lens certificateOrientation
      (p := 0) (x := -u) (y := -v) positive small c_nonnegative cotangent
    simpa only [sub_neg_eq_add, zero_add] using
      h (by simpa only [sub_neg_eq_add, zero_add] using c_positive)
  have on_panel (i : Fin m) : AffineMap.lineMap a b t - body i ∈ strictRayCone u v := by
    have test := List.all_eq_true.mp passed.2 i (List.mem_finRange i)
    simp only [Bool.and_eq_true] at test
    have before : a - body i ∈ strictRayCone u v := mem_strictRayCone_of_positive_orient det_pos
      (by simpa only [orient, PiLp.zero_apply, sub_zero] using
        CheckedReal.positive_of_isPositive hD _ test.1.1.1)
      (by simpa only [orient, PiLp.zero_apply, sub_zero] using
        CheckedReal.positive_of_isPositive hD _ test.1.1.2)
    have after : b - body i ∈ strictRayCone u v := mem_strictRayCone_of_positive_orient det_pos
      (by simpa only [orient, PiLp.zero_apply, sub_zero] using
        CheckedReal.positive_of_isPositive hD _ test.1.2)
      (by simpa only [orient, PiLp.zero_apply, sub_zero] using
        CheckedReal.positive_of_isPositive hD _ test.2)
    have transported : AffineMap.lineMap a b t - body i =
        AffineMap.lineMap (a - body i) (b - body i) t := by
      rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module']
      module
    rw [transported]
    exact strictRayCone_lineMap before after bounds
  have separate (k : Fin m) : AffineMap.lineMap a b t - body k ≠ 0 := by
    intro zero
    exact zero_not_mem_strictRayCone det_pos.ne' (zero ▸ on_panel k)
  exact (angle_le_angle_of_inDirectionWedge (separate i) (separate j)
    (strictRayCone_subset_directionWedge (on_panel i))
    (strictRayCone_subset_directionWedge (on_panel j))).trans_lt upper

/-- Check the angle of one fixed extreme pair along an entire panel. -/
def checkUpperExtremeBounds {c : ℝ} (coeff : CheckedReal D c) (i j : Fin m) : Bool :=
  let u := CheckedPlane.sub ca (vertices i)
  let v := CheckedPlane.sub ca (vertices j)
  let x := CheckedPlane.sub cb (vertices i)
  let y := CheckedPlane.sub cb (vertices j)
  let firstCross := CheckedPlane.det hD u v
  let lastCross := CheckedPlane.det hD x y
  let first := (CheckedPlane.dot hD u v).add (coeff.mul hD firstCross)
  let last := (CheckedPlane.dot hD x y).add (coeff.mul hD lastCross)
  let error := (CheckedReal.rat D (1 / 4)).mul hD (CheckedPlane.normSq hD (CheckedPlane.sub cb ca))
  firstCross.isPositive && lastCross.isPositive &&
    (first.sub error).isPositive && (last.sub error).isPositive

/-- X and Y remain on the same strictly ordered rays when viewed on this panel. -/
def checkRayOrderOnPanel (i j : Fin m) : Bool :=
  (CheckedPlane.det hD (CheckedPlane.sub ca (vertices i)) (CheckedPlane.sub ca (vertices j))).isPositive &&
    (CheckedPlane.det hD (CheckedPlane.sub cb (vertices i)) (CheckedPlane.sub cb (vertices j))).isPositive

/-- Test that the chosen vertices are extreme at both endpoints. -/
def checkUpperVisualExtremePanel {c : ℝ} (coeff : CheckedReal D c) (i j : Fin m) : Bool :=
  checkUpperExtremeBounds hD ca cb vertices coeff i j &&
    (List.finRange m).all fun k =>
      (decide (k = i) || checkRayOrderOnPanel hD ca cb vertices i k) &&
      (decide (k = j) || checkRayOrderOnPanel hD ca cb vertices k j)

private theorem orient_zero_view_lineMap (a b x y : Plane) (t : ℝ) :
    orient 0 (AffineMap.lineMap a b t - x) (AffineMap.lineMap a b t - y) =
      (1 - t) * orient 0 (a - x) (a - y) + t * orient 0 (b - x) (b - y) := by
  simp only [AffineMap.lineMap_apply_module', orient, PiLp.zero_apply, PiLp.add_apply,
    PiLp.smul_apply, PiLp.sub_apply, sub_zero, smul_eq_mul]
  ring

private theorem positive_interpolate {t x y : ℝ} (bounds : t ∈ Set.Icc 0 1)
    (first : 0 < x) (last : 0 < y) : 0 < (1 - t) * x + t * y := by
  rcases eq_or_lt_of_le bounds.1 with zero | pos
  · simpa only [← zero, sub_zero, one_mul, zero_mul, add_zero] using first
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr bounds.2) first.le)
      (mul_pos pos last)

private theorem orient_view_positive_of_endpoints {a b x y : Plane} {t : ℝ}
    (bounds : t ∈ Set.Icc 0 1)
    (first : 0 < orient 0 (a - x) (a - y))
    (last : 0 < orient 0 (b - x) (b - y)) :
    0 < orient 0 (AffineMap.lineMap a b t - x) (AffineMap.lineMap a b t - y) := by
  rw [orient_zero_view_lineMap]
  exact positive_interpolate bounds first last

/-- Whole-panel extreme-pair bounds combined with the endpoint ray orders. -/
theorem upperVisualAngle_of_extreme_bounds {c α : ℝ} (coeff : CheckedReal D c)
    (positive : 0 < α) (small : α ≤ π / 2) (c_nonnegative : 0 ≤ c)
    (cotangent : c * sin α < cos α) (i j : Fin m)
    (passed : checkUpperExtremeBounds hD ca cb vertices coeff i j = true)
    (left : ∀ k, k ≠ i →
      0 < orient 0 (a - body i) (a - body k) ∧ 0 < orient 0 (b - body i) (b - body k))
    (right : ∀ k, k ≠ j →
      0 < orient 0 (a - body k) (a - body j) ∧ 0 < orient 0 (b - body k) (b - body j))
    {t : ℝ} (bounds : t ∈ Set.Icc 0 1) (k l : Fin m) :
    angle (AffineMap.lineMap a b t - body k) (AffineMap.lineMap a b t - body l) < π - α := by
  unfold checkUpperExtremeBounds at passed
  dsimp only at passed
  simp only [Bool.and_eq_true] at passed
  let ray (k : Fin m) := AffineMap.lineMap a b t - body k
  have as_orient {u v : Plane} (x : CheckedPlane D u) (y : CheckedPlane D v)
      (h : (CheckedPlane.det hD x y).isPositive = true) : 0 < orient 0 u v := by
    simpa only [orient, PiLp.zero_apply, sub_zero] using
      CheckedReal.positive_of_isPositive hD _ h
  have det_pos : 0 < orient 0 (ray i) (ray j) :=
    orient_view_positive_of_endpoints bounds
      (as_orient _ _ passed.1.1.1) (as_orient _ _ passed.1.1.2)
  have first : ‖b - a‖ ^ 2 / 4 <
      visualPairPolynomial certificateOrientation c a (body i) (body j) := by
    have h := CheckedReal.positive_of_isPositive hD _ passed.1.2
    rw [visualPairPolynomial, areaForm_certificateOrientation]
    push_cast at h
    linarith
  have last : ‖b - a‖ ^ 2 / 4 <
      visualPairPolynomial certificateOrientation c b (body i) (body j) := by
    have h := CheckedReal.positive_of_isPositive hD _ passed.2
    rw [visualPairPolynomial, areaForm_certificateOrientation]
    push_cast at h
    linarith
  have det_area : 0 < certificateOrientation.areaForm (ray i) (ray j) := by
    simpa only [areaForm_certificateOrientation, orient, PiLp.zero_apply, sub_zero] using det_pos
  have upper : angle (ray i) (ray j) < π - α := by
    apply visualAngle_lt_supplement_of_outside_lens certificateOrientation positive small
      c_nonnegative cotangent
    rw [abs_of_pos det_area, ← visualPairPolynomial, AffineMap.lineMap_apply_module', add_comm,
      visualPairPolynomial_segment]
    have lerp := positive_interpolate bounds (sub_pos.mpr first) (sub_pos.mpr last)
    have quadratic : t * (1 - t) * ‖b - a‖ ^ 2 ≤ ‖b - a‖ ^ 2 / 4 := by
      have h := mul_le_mul_of_nonneg_right (show t * (1 - t) ≤ 1 / 4 by nlinarith [sq_nonneg (t - 1 / 2)])
        (sq_nonneg ‖b - a‖)
      linarith
    linarith
  have nonzero_first : ray i ≠ 0 := by
    intro zero
    simp [zero, orient] at det_pos
  have nonzero_last : ray j ≠ 0 := by
    intro zero
    simp [zero, orient] at det_pos
  have in_wedge (k : Fin m) : ray k ≠ 0 ∧ InDirectionWedge (ray i) (ray j) (ray k) := by
    by_cases ki : k = i
    · subst k
      exact ⟨nonzero_first, 1, 0, zero_le_one, le_rfl, by simp⟩
    by_cases kj : k = j
    · subst k
      exact ⟨nonzero_last, 0, 1, le_rfl, zero_le_one, by simp⟩
    have first := orient_view_positive_of_endpoints bounds (left k ki).1 (left k ki).2
    have last := orient_view_positive_of_endpoints bounds (right k kj).1 (right k kj).2
    have strict := mem_strictRayCone_of_positive_orient det_pos first last
    exact ⟨fun z => zero_not_mem_strictRayCone det_pos.ne' (z ▸ strict),
      strictRayCone_subset_directionWedge strict⟩
  exact (angle_le_angle_of_inDirectionWedge (in_wedge k).1 (in_wedge l).1
    (in_wedge k).2 (in_wedge l).2).trans_lt upper

theorem rayOrderOnPanel_of_check (i j : Fin m)
    (passed : checkRayOrderOnPanel hD ca cb vertices i j = true) :
    0 < orient 0 (a - body i) (a - body j) ∧ 0 < orient 0 (b - body i) (b - body j) := by
  rw [checkRayOrderOnPanel, Bool.and_eq_true] at passed
  simpa only [orient, PiLp.zero_apply, sub_zero] using
    And.intro (CheckedReal.positive_of_isPositive hD _ passed.1)
      (CheckedReal.positive_of_isPositive hD _ passed.2)

/-- Unstructured bodies can certify both extreme vertices by checking all orders. -/
theorem upperVisualAngle_of_checked_extreme_panel {c α : ℝ} (coeff : CheckedReal D c)
    (positive : 0 < α) (small : α ≤ π / 2) (c_nonnegative : 0 ≤ c)
    (cotangent : c * sin α < cos α) (i j : Fin m)
    (passed : checkUpperVisualExtremePanel hD ca cb vertices coeff i j = true)
    {t : ℝ} (bounds : t ∈ Set.Icc 0 1) (k l : Fin m) :
    angle (AffineMap.lineMap a b t - body k) (AffineMap.lineMap a b t - body l) < π - α := by
  rw [checkUpperVisualExtremePanel, Bool.and_eq_true] at passed
  apply upperVisualAngle_of_extreme_bounds hD ca cb vertices coeff positive small c_nonnegative
    cotangent i j passed.1 _ _ bounds k l
  · intro g different
    have h := List.all_eq_true.mp passed.2 g (List.mem_finRange g)
    simp only [Bool.and_eq_true, different, decide_false, Bool.false_or] at h
    exact rayOrderOnPanel_of_check hD ca cb vertices i g h.1
  · intro g different
    have h := List.all_eq_true.mp passed.2 g (List.mem_finRange g)
    simp only [Bool.and_eq_true, different, decide_false, Bool.false_or] at h
    exact rayOrderOnPanel_of_check hD ca cb vertices g j h.2

/-- For a convex cyclic body, each extreme vertex needs only its two neighbors. -/
def checkUpperVisualConvexPanel (next : Equiv.Perm (Fin m)) {c : ℝ}
    (coeff : CheckedReal D c) (i j : Fin m) : Bool :=
  checkUpperExtremeBounds hD ca cb vertices coeff i j &&
    checkRayOrderOnPanel hD ca cb vertices i (next.symm i) &&
    checkRayOrderOnPanel hD ca cb vertices i (next i) &&
    checkRayOrderOnPanel hD ca cb vertices (next.symm j) j &&
    checkRayOrderOnPanel hD ca cb vertices (next j) j

private theorem convex_ray_order_left {I : Type*} {p : I → Plane} {next : Equiv.Perm I}
    (convex : CyclicConvexVertices p next) (q : Plane) (i k : I) (different : p k ≠ p i)
    (previous : 0 < orient 0 (q - p i) (q - p (next.symm i)))
    (following : 0 < orient 0 (q - p i) (q - p (next i))) :
    0 < orient 0 (q - p i) (q - p k) := by
  let L : Plane →ₗ[ℝ] ℝ := -certificateOrientation.areaForm (q - p i)
  have form (j) : L (p j - p i) = orient 0 (q - p i) (q - p j) := by
    simp only [L, LinearMap.neg_apply, areaForm_certificateOrientation, orient, PiLp.zero_apply,
      PiLp.sub_apply, sub_zero]
    ring
  have h := convex.pos_from_neighbors i L
    (by rwa [form]) (by rwa [form]) k different
  rwa [form] at h

private theorem convex_ray_order_right {I : Type*} {p : I → Plane} {next : Equiv.Perm I}
    (convex : CyclicConvexVertices p next) (q : Plane) (i k : I) (different : p k ≠ p i)
    (previous : 0 < orient 0 (q - p (next.symm i)) (q - p i))
    (following : 0 < orient 0 (q - p (next i)) (q - p i)) :
    0 < orient 0 (q - p k) (q - p i) := by
  let L : Plane →ₗ[ℝ] ℝ := certificateOrientation.areaForm (q - p i)
  have form (j) : L (p j - p i) = orient 0 (q - p j) (q - p i) := by
    simp only [L, areaForm_certificateOrientation, orient, PiLp.zero_apply, PiLp.sub_apply,
      sub_zero]
    ring
  have h := convex.pos_from_neighbors i L
    (by rwa [form]) (by rwa [form]) k different
  rwa [form] at h

/-- The two-neighbor test certifies every pair along the panel. -/
theorem upperVisualAngle_of_checked_convex_panel {next : Equiv.Perm (Fin m)}
    (convex : CyclicConvexVertices body next) (distinct : Function.Injective body)
    {c α : ℝ} (coeff : CheckedReal D c)
    (positive : 0 < α) (small : α ≤ π / 2) (c_nonnegative : 0 ≤ c)
    (cotangent : c * sin α < cos α) (i j : Fin m)
    (passed : checkUpperVisualConvexPanel hD ca cb vertices next coeff i j = true)
    {t : ℝ} (bounds : t ∈ Set.Icc 0 1) (k l : Fin m) :
    angle (AffineMap.lineMap a b t - body k) (AffineMap.lineMap a b t - body l) < π - α := by
  simp only [checkUpperVisualConvexPanel, Bool.and_eq_true] at passed
  have ip := rayOrderOnPanel_of_check hD ca cb vertices i (next.symm i) passed.1.1.1.2
  have inext := rayOrderOnPanel_of_check hD ca cb vertices i (next i) passed.1.1.2
  have jp := rayOrderOnPanel_of_check hD ca cb vertices (next.symm j) j passed.1.2
  have jnext := rayOrderOnPanel_of_check hD ca cb vertices (next j) j passed.2
  apply upperVisualAngle_of_extreme_bounds hD ca cb vertices coeff positive small c_nonnegative
    cotangent i j passed.1.1.1.1 _ _ bounds k l
  · intro g different
    exact ⟨convex_ray_order_left convex a i g (distinct.ne different) ip.1 inext.1,
      convex_ray_order_left convex b i g (distinct.ne different) ip.2 inext.2⟩
  · intro g different
    exact ⟨convex_ray_order_right convex a j g (distinct.ne different) jp.1 jnext.1,
      convex_ray_order_right convex b j g (distinct.ne different) jp.2 jnext.2⟩

/-- An interval uses either a fixed pair of extreme body vertices or two
rational rays enclosing every body vertex. -/
structure UpperVisualPanel (V : ℕ) where
  left : ℚ
  right : ℚ
  witness : (Fin V × Fin V) ⊕ ((ℚ × ℚ) × (ℚ × ℚ))

namespace UpperVisualPanel

variable {V : ℕ}

def endpoints (panel : UpperVisualPanel V) : ℚ × ℚ := (panel.left, panel.right)

def check {D : ℕ} (hD : 0 < D) {a b : Plane} {c : ℝ} {body : Fin V → Plane}
    (coeff : CheckedReal D c) (ca : CheckedPlane D a) (cb : CheckedPlane D b)
    (vertices : ∀ i, CheckedPlane D (body i)) (panel : UpperVisualPanel V) : Bool :=
  let left := checkSidePoint hD ca cb panel.left
  let right := checkSidePoint hD ca cb panel.right
  match panel.witness with
  | .inl (i, j) => checkUpperVisualExtremePanel hD left right vertices coeff i j
  | .inr (u, v) =>
    checkUpperVisualPanel hD (CheckedPlane.rat D u.1 u.2) (CheckedPlane.rat D v.1 v.2)
      left right vertices coeff

/-- Use two-neighbor tests for fixed extreme vertices on a convex body. -/
def checkConvex {D : ℕ} (hD : 0 < D) {a b : Plane} {c : ℝ} {body : Fin V → Plane}
    (next : Equiv.Perm (Fin V))
    (coeff : CheckedReal D c) (ca : CheckedPlane D a) (cb : CheckedPlane D b)
    (vertices : ∀ i, CheckedPlane D (body i)) (panel : UpperVisualPanel V) : Bool :=
  let left := checkSidePoint hD ca cb panel.left
  let right := checkSidePoint hD ca cb panel.right
  match panel.witness with
  | .inl (i, j) => checkUpperVisualConvexPanel hD left right vertices next coeff i j
  | .inr (u, v) =>
    checkUpperVisualPanel hD (CheckedPlane.rat D u.1 u.2) (CheckedPlane.rat D v.1 v.2)
      left right vertices coeff

private theorem angle_lt_of_cover {a b : Plane} {body : Fin V → Plane} {α : ℝ}
    (panels : List (UpperVisualPanel V)) (nonempty : panels ≠ [])
    (cover : coversRationalPanels endpoints 0 panels = true)
    (valid : ∀ w ∈ panels, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ k l : Fin V,
      let point := AffineMap.lineMap (AffineMap.lineMap a b (w.left : ℝ))
        (AffineMap.lineMap a b (w.right : ℝ)) s
      angle (point - body k) (point - body l) < π - α)
    {t : ℝ} (bounds : t ∈ Set.Icc 0 1) (k l : Fin V) :
    angle (AffineMap.lineMap a b t - body k) (AffineMap.lineMap a b t - body l) < π - α := by
  obtain ⟨⟨left, right, witness⟩, member, ordered, t_bounds⟩ :=
    mem_cover_of_rationalPanels endpoints panels nonempty cover (by simpa using bounds)
  change left < right at ordered
  change t ∈ Set.Icc (left : ℝ) (right : ℝ) at t_bounds
  let s := (t - (left : ℝ)) / ((right : ℝ) - (left : ℝ))
  have length : 0 < (right : ℝ) - (left : ℝ) := sub_pos.mpr (by exact_mod_cast ordered)
  have s_bounds : s ∈ Set.Icc 0 1 :=
    ⟨div_nonneg (sub_nonneg.mpr t_bounds.1) length.le,
      (div_le_one length).mpr (sub_le_sub_right t_bounds.2 _)⟩
  have parameter : t = (1 - s) * (left : ℝ) + s * (right : ℝ) := by
    dsimp [s]
    field_simp [length.ne']
    ring
  have point : AffineMap.lineMap a b t =
      AffineMap.lineMap (AffineMap.lineMap a b (left : ℝ))
        (AffineMap.lineMap a b (right : ℝ)) s := by
    conv_lhs => rw [parameter]
    simp only [AffineMap.lineMap_apply_module']
    module
  rw [point]
  exact valid ⟨left, right, witness⟩ member s s_bounds k l

/-- A passed hybrid certificate enforces the upper aperture at every point
of the whole side. -/
theorem angle_lt_of_checked_cover {D : ℕ} (hD : 0 < D) {a b : Plane}
    {body : Fin V → Plane} {c α : ℝ} (coeff : CheckedReal D c)
    (ca : CheckedPlane D a) (cb : CheckedPlane D b)
    (vertices : ∀ i, CheckedPlane D (body i))
    (positive : 0 < α) (small : α ≤ π / 2) (c_nonnegative : 0 ≤ c)
    (cotangent : c * sin α < cos α)
    (panels : List (UpperVisualPanel V)) (nonempty : panels ≠ [])
    (cover : coversRationalPanels endpoints 0 panels = true)
    (passed : panels.all (check hD coeff ca cb vertices) = true)
    {t : ℝ} (bounds : t ∈ Set.Icc 0 1) (k l : Fin V) :
    angle (AffineMap.lineMap a b t - body k) (AffineMap.lineMap a b t - body l) < π - α := by
  apply angle_lt_of_cover panels nonempty cover _ bounds k l
  intro panel member s s_bounds k l
  rcases panel with ⟨left, right, witness⟩
  have test := List.all_eq_true.mp passed _ member
  let cl := checkSidePoint hD ca cb left
  let cr := checkSidePoint hD ca cb right
  rcases witness with ⟨i, j⟩ | ⟨u, v⟩
  · exact upperVisualAngle_of_checked_extreme_panel hD cl cr vertices coeff positive small
      c_nonnegative cotangent i j test s_bounds k l
  · exact upperVisualAngle_of_checked_panel hD
      (CheckedPlane.rat D u.1 u.2) (CheckedPlane.rat D v.1 v.2) cl cr vertices coeff
      positive small c_nonnegative cotangent test s_bounds k l

/-- The convex-body hybrid certificate enforces the upper aperture on the whole side. -/
theorem angle_lt_of_checked_convex_cover {D : ℕ} (hD : 0 < D) {a b : Plane}
    {body : Fin V → Plane} {next : Equiv.Perm (Fin V)}
    (convex : CyclicConvexVertices body next) (distinct : Function.Injective body)
    {c α : ℝ} (coeff : CheckedReal D c)
    (ca : CheckedPlane D a) (cb : CheckedPlane D b)
    (vertices : ∀ i, CheckedPlane D (body i))
    (positive : 0 < α) (small : α ≤ π / 2) (c_nonnegative : 0 ≤ c)
    (cotangent : c * sin α < cos α)
    (panels : List (UpperVisualPanel V)) (nonempty : panels ≠ [])
    (cover : coversRationalPanels endpoints 0 panels = true)
    (passed : panels.all (checkConvex hD next coeff ca cb vertices) = true)
    {t : ℝ} (bounds : t ∈ Set.Icc 0 1) (k l : Fin V) :
    angle (AffineMap.lineMap a b t - body k) (AffineMap.lineMap a b t - body l) < π - α := by
  apply angle_lt_of_cover panels nonempty cover _ bounds k l
  intro panel member s s_bounds k l
  rcases panel with ⟨left, right, witness⟩
  have test := List.all_eq_true.mp passed _ member
  let cl := checkSidePoint hD ca cb left
  let cr := checkSidePoint hD ca cb right
  rcases witness with ⟨i, j⟩ | ⟨u, v⟩
  · exact upperVisualAngle_of_checked_convex_panel hD cl cr vertices convex distinct coeff positive small
      c_nonnegative cotangent i j test s_bounds k l
  · exact upperVisualAngle_of_checked_panel hD
      (CheckedPlane.rat D u.1 u.2) (CheckedPlane.rat D v.1 v.2) cl cr vertices coeff
      positive small c_nonnegative cotangent test s_bounds k l

end UpperVisualPanel

end Unfoldings.FewestNets
