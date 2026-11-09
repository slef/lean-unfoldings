module

public import Unfoldings.Cone.AngularChord
public import Unfoldings.Cone.HeadingSector
public import Unfoldings.Cone.HeadingEquality

/-!
# Lifting a selected pointed sector in any angular fan

A bounded real heading interval selects the intended copies of rays even in
a development with overlap. Only pieces meeting that interval participate in
the inverse bound. Their widths and the interval width are less than pi,
so a shared planar point has the same real heading on the participating pieces.

The constructed lift is isometric on the whole selected convex sector. No
bound on the total fan angle or global nonoverlap is required.
-/

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n)

def IsHeadingRepresentative (a b : ℝ) (z : ℂ) (p : MetricGluing.Total A.Cell) : Prop :=
  A.place p.1 p.2 = z ∧ ∃ r : ℝ≥0, ∃ θ ∈ Set.Icc a b,
    θ ∈ Set.Icc (A.heading p.1.castSucc) (A.heading p.1.succ) ∧
      A.place p.1 p.2 = (r : ℂ) * polarRay θ

theorem exists_headingRepresentative (a b : ℝ) (positive : 0 < b - a)
    (small : b - a < Real.pi) (first : 0 ≤ a) (last : b ≤ A.totalAngle)
    (z : headingSector a b) : ∃ p, A.IsHeadingRepresentative a b z.val p := by
  obtain ⟨r, θ, bounds, equal⟩ :=
    (mem_headingSector_iff_polar a b positive small z.val).mp z.property
  obtain ⟨i, interval⟩ := A.exists_closed_heading_piece θ
    ⟨first.trans bounds.1, bounds.2.trans last⟩
  obtain ⟨w, inside, image⟩ := (A.mem_faceImage_iff i z.val).mpr ⟨r, θ, interval, equal⟩
  exact ⟨⟨i, ⟨w, inside⟩⟩, image, r, θ, bounds, interval, image.trans equal⟩

def headingRepresentative (a b : ℝ) (positive : 0 < b - a)
    (small : b - a < Real.pi) (first : 0 ≤ a) (last : b ≤ A.totalAngle)
    (z : headingSector a b) : MetricGluing.Total A.Cell :=
  (A.exists_headingRepresentative a b positive small first last z).choose

theorem headingRepresentative_spec (a b : ℝ) (positive : 0 < b - a)
    (small : b - a < Real.pi) (first : 0 ≤ a) (last : b ≤ A.totalAngle)
    (z : headingSector a b) :
    A.IsHeadingRepresentative a b z.val
      (A.headingRepresentative a b positive small first last z) :=
  (A.exists_headingRepresentative a b positive small first last z).choose_spec

/-- The lift follows the selected real heading interval, including its banks. -/
def headingLift (a b : ℝ) (positive : 0 < b - a)
    (small : b - a < Real.pi) (first : 0 ≤ a) (last : b ≤ A.totalAngle)
    (z : headingSector a b) : A.Surface :=
  MetricGluing.point A.Cell A.glue (A.headingRepresentative a b positive small first last z)

@[simp] theorem develop_headingLift (a b : ℝ) (positive : 0 < b - a)
    (small : b - a < Real.pi) (first : 0 ≤ a) (last : b ≤ A.totalAngle)
    (z : headingSector a b) :
    A.develop (A.headingLift a b positive small first last z) = z.val :=
  (A.headingRepresentative_spec a b positive small first last z).1

theorem headingLift_place (a b : ℝ) (positive : 0 < b - a)
    (small : b - a < Real.pi) (first : 0 ≤ a) (last : b ≤ A.totalAngle)
    (i : Fin (n + 1)) (x : A.Cell i)
    (inside : A.place i x ∈ headingSector a b)
    (meets : A.heading i.castSucc ≤ b ∧ a ≤ A.heading i.succ) :
    A.headingLift a b positive small first last ⟨A.place i x, inside⟩ = A.faceMap i x := by
  let z : headingSector a b := ⟨A.place i x, inside⟩
  let p := A.headingRepresentative a b positive small first last z
  have spec := A.headingRepresentative_spec a b positive small first last z
  change A.place p.1 p.2 = A.place i x ∧ _ at spec
  obtain ⟨image, r, θ, band, interval, coordinates⟩ := spec
  change A.faceMap p.1 p.2 = A.faceMap i x
  by_cases zero : A.place i x = 0
  · exact (A.faceMap_eq_origin_of_place_zero p.1 p.2 (image.trans zero)).trans
      (A.faceMap_eq_origin_of_place_zero i x zero).symm
  · obtain ⟨s, φ, φbounds, φcoordinates⟩ := A.exists_place_polar i x
    have radii : r = s :=
      polar_radius_eq r s θ φ (coordinates.symm.trans (image.trans φcoordinates))
    subst s
    have nonzero : r ≠ 0 := by
      intro radius_zero
      apply zero
      rw [φcoordinates, radius_zero]
      simp
    have width : A.heading i.succ - A.heading i.castSucc < Real.pi := by
      rw [A.heading_succ, add_sub_cancel_left]
      exact A.small i
    have same : θ = φ := polar_eq_heading_of_overlapping_intervals r nonzero
      a b (A.heading i.castSucc) (A.heading i.succ) small width meets.2 meets.1 θ φ band φbounds
      (coordinates.symm.trans (image.trans φcoordinates))
    rw [← same] at φbounds φcoordinates
    exact A.faceMap_eq_of_same_heading p.1 i p.2 x r θ interval φbounds coordinates φcoordinates

theorem headingLift_lipschitz (a b : ℝ) (positive : 0 < b - a)
    (small : b - a < Real.pi) (first : 0 ≤ a) (last : b ≤ A.totalAngle) :
    LipschitzWith 1 (A.headingLift a b positive small first last) := by
  classical
  let domain := headingSector a b
  let lift := A.headingLift a b positive small first last
  let meets (i : Fin (n + 1)) := A.heading i.castSucc ≤ b ∧ a ≤ A.heading i.succ
  let pieces (i : Fin (n + 1)) : Set domain :=
    if meets i then Subtype.val ⁻¹' A.faceImage i else ∅
  have closed (i : Fin (n + 1)) : IsClosed (pieces i) := by
    by_cases hi : meets i
    · simpa only [pieces, ite_eq_left hi] using
        (A.isClosed_faceImage i).preimage
          (continuous_subtype_val : Continuous (Subtype.val : domain → ℂ))
    · simpa only [pieces, ite_eq_right hi] using (isClosed_empty : IsClosed (∅ : Set domain))
  have cover : ⋃ i, pieces i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    let p := A.headingRepresentative a b positive small first last z
    obtain ⟨image, r, θ, band, interval, coordinates⟩ :=
      A.headingRepresentative_spec a b positive small first last z
    have hi : meets p.1 := ⟨interval.1.trans band.2, band.1.trans interval.2⟩
    apply Set.mem_iUnion.mpr
    refine ⟨p.1, ?_⟩
    simp only [pieces, ite_eq_left hi, Set.mem_preimage]
    exact ⟨p.2.val, p.2.property, image⟩
  have bounded (i : Fin (n + 1)) : LipschitzOnWith 1 lift (pieces i) := by
    intro z hz w hw
    have hi : meets i := by
      by_contra no
      simp only [pieces, ite_eq_right no, Set.mem_empty_iff_false] at hz
    have hz' : z.val ∈ A.faceImage i := by
      simpa only [pieces, ite_eq_left hi, Set.mem_preimage] using hz
    have hw' : w.val ∈ A.faceImage i := by
      simpa only [pieces, ite_eq_left hi, Set.mem_preimage] using hw
    obtain ⟨left_point, hl, left_equal⟩ := hz'
    obtain ⟨right_point, hr, right_equal⟩ := hw'
    let x : A.Cell i := ⟨left_point, hl⟩
    let y : A.Cell i := ⟨right_point, hr⟩
    have left_coordinates : A.place i x = z.val := left_equal
    have right_coordinates : A.place i y = w.val := right_equal
    have left_preimage : lift z = A.faceMap i x := by
      have inside : A.place i x ∈ headingSector a b := by rw [left_coordinates]; exact z.property
      have equal : (⟨A.place i x, inside⟩ : domain) = z := Subtype.ext left_coordinates
      exact (congrArg lift equal).symm.trans
        (A.headingLift_place a b positive small first last i x inside hi)
    have right_preimage : lift w = A.faceMap i y := by
      have inside : A.place i y ∈ headingSector a b := by rw [right_coordinates]; exact w.property
      have equal : (⟨A.place i y, inside⟩ : domain) = w := Subtype.ext right_coordinates
      exact (congrArg lift equal).symm.trans
        (A.headingLift_place a b positive small first last i y inside hi)
    change edist (lift z) (lift w) ≤ (1 : ℝ≥0∞) * edist z.val w.val
    rw [one_mul, left_preimage, right_preimage, ← left_coordinates, ← right_coordinates]
    exact ((A.faceMap_isometry i x y).trans (A.place_isometry i x y).symm).le
  exact convex_subtype_lipschitzWith_of_finite_closed_cover domain
    (convex_headingSector a b) pieces closed cover lift 1 bounded

/-- A selected pointed heading sector embeds isometrically in any fan,
including one whose full development overlaps. -/
theorem headingLift_isometry (a b : ℝ) (positive : 0 < b - a)
    (small : b - a < Real.pi) (first : 0 ≤ a) (last : b ≤ A.totalAngle) :
    Isometry (A.headingLift a b positive small first last) := by
  intro z w
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using
      (A.headingLift_lipschitz a b positive small first last).edist_le_mul z w
  · have bound := A.develop_lipschitz.edist_le_mul
      (A.headingLift a b positive small first last z)
      (A.headingLift a b positive small first last w)
    change edist z.val w.val ≤ _
    simpa only [A.develop_headingLift, ENNReal.coe_one, one_mul] using bound

end Unfoldings.AngularFan
