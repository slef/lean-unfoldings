module

public import Unfoldings.FewestNets.CheckedPlane
public import Unfoldings.FewestNets.VisualCertificate

/-! Certify a strict lower visual angle over an entire polygon side. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry Real Module

local instance : Fact (finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Orientation associated with the certificate's ordered orthonormal axes. -/
def certificateOrientation : Orientation ℝ Plane (Fin 2) :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation

theorem areaForm_certificateOrientation (x y : Plane) :
    certificateOrientation.areaForm x y = x 0 * y 1 - x 1 * y 0 := by
  let B := EuclideanSpace.basisFun (Fin 2) ℝ
  have form := certificateOrientation.volumeForm_robust B rfl
  rw [certificateOrientation.areaForm_to_volumeForm, form, Basis.det_apply, Matrix.det_fin_two,
    Basis.toMatrix_apply, Basis.toMatrix_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  simp only [OrthonormalBasis.coe_toBasis_repr_apply, B, EuclideanSpace.basisFun_repr,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_comm (y 0) (x 1)]

/-- A pair and a sign witness one subinterval of a side. -/
structure SideVisualWitness (V : ℕ) where
  left : ℚ
  right : ℚ
  first : Fin V
  last : Fin V
  positiveSign : Bool

/-- A contiguous rational cover of the remainder of the unit interval. -/
def coversRationalPanels {W : Type*} (endpoints : W → ℚ × ℚ) (cursor : ℚ) :
    List W → Bool
  | [] => decide (cursor = 1)
  | w :: ws =>
    decide ((endpoints w).1 = cursor) && decide ((endpoints w).1 < (endpoints w).2) &&
      coversRationalPanels endpoints (endpoints w).2 ws

theorem mem_cover_of_rationalPanels {W : Type*} (endpoints : W → ℚ × ℚ) (ws : List W)
    (nonempty : ws ≠ []) {cursor : ℚ} (check : coversRationalPanels endpoints cursor ws = true)
    {t : ℝ} (ht : t ∈ Set.Icc (cursor : ℝ) 1) :
    ∃ w ∈ ws, (endpoints w).1 < (endpoints w).2 ∧
      t ∈ Set.Icc ((endpoints w).1 : ℝ) ((endpoints w).2 : ℝ) := by
  induction ws generalizing cursor with
  | nil => exact (nonempty rfl).elim
  | cons w ws ih =>
    simp only [coversRationalPanels, Bool.and_eq_true, decide_eq_true_eq] at check
    have left : (endpoints w).1 = cursor := check.1.1
    by_cases right : t ≤ ((endpoints w).2 : ℝ)
    · exact ⟨w, List.mem_cons_self, check.1.2, by rw [left]; exact ⟨ht.1, right⟩⟩
    · by_cases empty : ws = []
      · have eq : (endpoints w).2 = 1 := by simpa [empty, coversRationalPanels] using check.2
        exact (right (by simpa [eq] using ht.2)).elim
      · obtain ⟨v, hv, ordered, htv⟩ := ih empty check.2 ⟨le_of_not_ge right, ht.2⟩
        exact ⟨v, List.mem_cons_of_mem _ hv, ordered, htv⟩

def SideVisualWitness.coversFrom {V : ℕ} :=
  coversRationalPanels (fun w : SideVisualWitness V => (w.left, w.right))

theorem SideVisualWitness.mem_cover_of_check {V : ℕ} (ws : List (SideVisualWitness V))
    (nonempty : ws ≠ []) {cursor : ℚ} (check : coversFrom cursor ws = true) {t : ℝ}
    (ht : t ∈ Set.Icc (cursor : ℝ) 1) :
    ∃ w ∈ ws, w.left < w.right ∧ t ∈ Set.Icc (w.left : ℝ) (w.right : ℝ) :=
  mem_cover_of_rationalPanels (fun w : SideVisualWitness V => (w.left, w.right))
    ws nonempty (cursor := cursor) check ht

/-- Checked interpolation of the side coordinates at an exact rational parameter. -/
def checkSidePoint {D : ℕ} (hD : 0 < D) {p q : Plane}
    (cp : CheckedPlane D p) (cq : CheckedPlane D q) (t : ℚ) :
    CheckedPlane D (AffineMap.lineMap p q (t : ℝ)) :=
  let ct := CheckedReal.rat D t
  let one : CheckedReal D (1 : ℝ) := (CheckedReal.rat D 1).convert (by simp)
  let point := CheckedPlane.add (CheckedPlane.smul hD (one.sub ct) cp)
    (CheckedPlane.smul hD ct cq)
  fun i => (point i).convert (by rw [AffineMap.lineMap_apply_module])

/-- Checked enclosure of the signed pair test at one exact rational parameter. -/
def checkVisualEndpoint {D : ℕ} (hD : 0 < D) {u v p q : Plane} {c : ℝ}
    (cx : CheckedReal D c) (cu : CheckedPlane D u) (cv : CheckedPlane D v)
    (cp : CheckedPlane D p) (cq : CheckedPlane D q) (t : ℚ) :
    CheckedReal D (visualPairPolynomial certificateOrientation c
      (AffineMap.lineMap p q (t : ℝ)) u v) :=
  let point := checkSidePoint hD cp cq t
  let a := CheckedPlane.sub point cu
  let b := CheckedPlane.sub point cv
  ((CheckedPlane.dot hD a b).add (cx.mul hD (CheckedPlane.det hD a b))).convert (by
    rw [visualPairPolynomial, areaForm_certificateOrientation])

/-- Endpoint signs for one saved panel imply its desired angle at every
point of the panel. The original certificate uses either witness sign. -/
theorem lowerVisualAngle_of_panel {a c left right t : ℝ} {p q x y : Plane}
    (a_pos : 0 < a) (a_small : a ≤ π / 2) (cot : |c| * sin a < cos a)
    (ordered : left < right) (member : t ∈ Set.Icc left right)
    (first : visualPairPolynomial certificateOrientation c (AffineMap.lineMap p q left) x y < 0)
    (last : visualPairPolynomial certificateOrientation c (AffineMap.lineMap p q right) x y < 0) :
    a < angle (AffineMap.lineMap p q t - x) (AffineMap.lineMap p q t - y) := by
  let s := (t - left) / (right - left)
  have pos : 0 < right - left := sub_pos.mpr ordered
  have s_lo : 0 ≤ s := div_nonneg (sub_nonneg.mpr member.1) pos.le
  have s_hi : s ≤ 1 := (div_le_one pos).mpr (sub_le_sub_right member.2 _)
  have combine : t = (1 - s) * left + s * right := by
    dsimp [s]
    field_simp [pos.ne']
    ring
  have point : AffineMap.lineMap p q t =
      AffineMap.lineMap p q left +
        s • (AffineMap.lineMap p q right - AffineMap.lineMap p q left) := by
    rw [combine, AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module',
      AffineMap.lineMap_apply_module']
    module
  apply visualAngle_lt_of_pair_polynomial certificateOrientation a_pos a_small cot
  rw [point]
  exact visualPairPolynomial_segment_lt_zero certificateOrientation first last s_lo s_hi

namespace SideVisualWitness

variable {V : ℕ}

def signedCot (positive : Bool) (c : ℝ) : ℝ := if positive then c else -c

def checkSignedCot {D : ℕ} {c : ℝ} (cx : CheckedReal D c) (positive : Bool) :
    CheckedReal D (signedCot positive c) :=
  match positive with
  | false => cx.neg
  | true => cx

/-- Check that the saved pair polynomial is negative at both rational endpoints. -/
def checkPanel {D : ℕ} (hD : 0 < D) {p q : Plane} {c : ℝ} {body : Fin V → Plane}
    (cs : CheckedReal D c) (cp : CheckedPlane D p) (cq : CheckedPlane D q)
    (cb : (i : Fin V) → CheckedPlane D (body i)) (w : SideVisualWitness V) : Bool :=
  let coef := checkSignedCot cs w.positiveSign
  (checkVisualEndpoint hD coef (cb w.first) (cb w.last) cp cq w.left).neg.isPositive &&
    (checkVisualEndpoint hD coef (cb w.first) (cb w.last) cp cq w.right).neg.isPositive

/-- A successful cover and all endpoint tests certify the whole closed side. -/
theorem lowerVisualAngle_of_check {D : ℕ} (hD : 0 < D)
    {p q : Plane} {a c : ℝ} {body : Fin V → Plane} (a_pos : 0 < a) (a_small : a ≤ π / 2)
    (c_nonneg : 0 ≤ c) (cot : c * sin a < cos a)
    (cs : CheckedReal D c) (cp : CheckedPlane D p) (cq : CheckedPlane D q)
    (cb : (i : Fin V) → CheckedPlane D (body i)) (ws : List (SideVisualWitness V))
    (nonempty : ws ≠ []) (cover : coversFrom 0 ws = true)
    (valid : ws.all (checkPanel hD cs cp cq cb) = true) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ∃ i j, a < angle (AffineMap.lineMap p q t - body i) (AffineMap.lineMap p q t - body j) := by
  obtain ⟨w, hw, ordered, member⟩ :=
    mem_cover_of_check ws nonempty cover (by simpa using ht)
  have h := List.all_eq_true.mp valid w hw
  rw [checkPanel, Bool.and_eq_true] at h
  have first := neg_pos.mp (CheckedReal.positive_of_isPositive hD _ h.1)
  have last := neg_pos.mp (CheckedReal.positive_of_isPositive hD _ h.2)
  have slope : |signedCot w.positiveSign c| * sin a < cos a := by
    cases w.positiveSign <;> simpa [signedCot, abs_of_nonneg c_nonneg] using cot
  exact ⟨w.first, w.last, lowerVisualAngle_of_panel a_pos a_small slope
    (by exact_mod_cast ordered) member first last⟩

end SideVisualWitness
end Unfoldings.FewestNets
