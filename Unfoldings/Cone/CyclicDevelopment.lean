module

public import Unfoldings.Cone.ConsecutiveCompatibility
public import Unfoldings.Cone.CyclicSeams
public import Unfoldings.Cone.AngularOverlap
public import Unfoldings.Cone.AngularCoordinates

/-!
# Constructed planar developments of full-turn cyclic tangent fans

At every actual seam, the directed frames give equal-radius consecutive
banks or the two outer banks. The latter have coincident developed points
at a full turn. Thus the planar coordinates descend through the original
tangent route metric, without assuming a development or a spatial folding.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

def tangentPlaneCell {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (covers : ∀ p, chain.Visited p) (q : C.CornerAt retain v) (x : C.TangentCell retain v q) : ℂ :=
  (C.linkAngularFan retain v chain).develop (C.tangentCellToAngular retain v chain covers q x)

theorem tangentPlaneCell_lipschitz {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (covers : ∀ p, chain.Visited p) (q : C.CornerAt retain v) :
    LipschitzWith 1 (C.tangentPlaneCell retain v chain covers q) := by
  change LipschitzWith 1 ((C.linkAngularFan retain v chain).develop ∘
    C.tangentCellToAngular retain v chain covers q)
  simpa only [one_mul] using (C.linkAngularFan retain v chain).develop_lipschitz.comp
    (C.tangentCellToAngular_lipschitz retain v chain covers q)

theorem tangentPlaneCell_of_coordinates {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (q : C.CornerAt retain v) (x : C.TangentCell retain v q)
    (i : Fin (n + 1)) (y : (C.linkAngularFan retain v chain).Cell i)
    (corner : q.val = (chain.point i).val.1)
    (coordinates : C.germFrame (chain.point i).val x.val = y.val) :
    C.tangentPlaneCell retain v chain covers q x = (C.linkAngularFan retain v chain).place i y :=
  (congrArg (C.linkAngularFan retain v chain).develop
    (C.tangentCellToAngular_of_coordinates retain v chain covers q x i y corner coordinates)).trans
      ((C.linkAngularFan retain v chain).develop_faceMap i y)

theorem tangentPlaneCell_closing {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (full : (C.linkAngularFan retain v chain).totalAngle = 2 * Real.pi) (r : ℝ≥0)
    (a b : C.CornerAt retain v) (x : C.TangentCell retain v a) (y : C.TangentCell retain v b)
    (left_corner : a.val = chain.last.val.1) (right_corner : b.val = chain.first.val.1)
    (left_coordinates : C.germFrame chain.last.val x.val =
      (r : ℝ) • polarRay ((C.linkAngularFan retain v chain).angle (Fin.last n)))
    (right_coordinates : C.germFrame chain.first.val y.val = (r : ℂ)) :
    C.tangentPlaneCell retain v chain covers a x =
      C.tangentPlaneCell retain v chain covers b y := by
  calc
    _ = (C.linkAngularFan retain v chain).place (Fin.last n)
        ((C.linkAngularFan retain v chain).finish (Fin.last n) r) :=
      C.tangentPlaneCell_of_coordinates retain v chain covers a x _ _ left_corner left_coordinates
    _ = (C.linkAngularFan retain v chain).place 0 ((C.linkAngularFan retain v chain).start 0 r) :=
      (C.linkAngularFan retain v chain).outer_banks_coincide full r
    _ = _ := (C.tangentPlaneCell_of_coordinates retain v chain covers b y 0
      ((C.linkAngularFan retain v chain).start 0 r) right_corner right_coordinates).symm

theorem tangentPlaneCell_cyclic_compatible {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (closes : C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first)
    (full : (C.linkAngularFan retain v chain).totalAngle = 2 * Real.pi)
    (a b : MetricGluing.Total (C.TangentCell retain v)) (joined : C.tangentGlue retain v a b) :
    C.tangentPlaneCell retain v chain covers a.1 a.2 =
      C.tangentPlaneCell retain v chain covers b.1 b.2 := by
  obtain ⟨s, x, t, nonnegative, rfl, rfl⟩ := joined
  let r : ℝ≥0 := ⟨dist (C.tangentApex retain v (C.tangentLeft retain v s))
    (C.tangentLeftPoint retain v s x t nonnegative), dist_nonneg⟩
  rcases C.tangentSeam_cyclic_cases retain v chain covers closes s with
    ⟨k, source, target⟩ | ⟨k, source, target⟩ | ⟨source, target⟩ | ⟨source, target⟩
  · exact congrArg (C.linkAngularFan retain v chain).develop
      (C.tangentCellToAngular_seam_forward retain v chain covers k s x t nonnegative source target)
  · exact congrArg (C.linkAngularFan retain v chain).develop
      (C.tangentCellToAngular_seam_backward retain v chain covers k s x t nonnegative source target)
  · have left_corner : (C.tangentLeft retain v s).val = chain.last.val.1 := by
      have corners := congrArg (fun p : C.Germ => p.1) source
      exact corners
    have right_corner : (C.tangentRight retain v s).val = chain.first.val.1 :=
      congrArg Prod.fst target
    have turned : C.turnGerm (C.tangentSourceGerm retain v s) = chain.last.val :=
      (congrArg C.turnGerm source).trans (C.turnGerm_involutive _)
    have angle := congrArg (fun c : C.Corner => (C.triangle c.1).cornerAngle c.2) left_corner
    change (C.triangle (C.tangentLeft retain v s).val.1).cornerAngle
      (C.tangentLeft retain v s).val.2 =
        (C.linkAngularFan retain v chain).angle (Fin.last n) at angle
    have left_coordinates := C.germFrame_radial_left retain v s x t nonnegative
    rw [turned, angle] at left_coordinates
    have right_coordinates := C.germFrame_radial_right retain v s x t nonnegative
    rw [target, ← C.tangentRadialSeam_radius_eq retain v s x t nonnegative] at right_coordinates
    exact C.tangentPlaneCell_closing retain v chain covers full r _ _ _ _
      left_corner right_corner left_coordinates right_coordinates
  · have left_corner : (C.tangentRight retain v s).val = chain.last.val.1 := by
      have corners := congrArg (fun p : C.Germ => p.1) target
      exact corners
    have right_corner : (C.tangentLeft retain v s).val = chain.first.val.1 :=
      congrArg Prod.fst source
    have turned : C.turnGerm (C.tangentTargetGerm retain v s) = chain.last.val :=
      (congrArg C.turnGerm target).trans (C.turnGerm_involutive _)
    have angle := congrArg (fun c : C.Corner => (C.triangle c.1).cornerAngle c.2) left_corner
    change (C.triangle (C.tangentRight retain v s).val.1).cornerAngle
      (C.tangentRight retain v s).val.2 =
        (C.linkAngularFan retain v chain).angle (Fin.last n) at angle
    have left_coordinates := C.germFrame_radial_right_terminal retain v s x t nonnegative
    rw [turned, angle, ← C.tangentRadialSeam_radius_eq retain v s x t nonnegative]
      at left_coordinates
    have right_coordinates := C.germFrame_radial_left_initial retain v s x t nonnegative
    rw [source] at right_coordinates
    exact (C.tangentPlaneCell_closing retain v chain covers full r _ _ _ _
      left_corner right_corner left_coordinates right_coordinates).symm

/-- The full-turn cyclic development is constructed from the actual tangent gluing. -/
def cyclicDevelopment {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (closes : C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first)
    (full : (C.linkAngularFan retain v chain).totalAngle = 2 * Real.pi) :
    C.TangentFan retain v → ℂ :=
  MetricGluing.lift (C.TangentCell retain v) (C.tangentGlue retain v)
    (C.tangentPlaneCell retain v chain covers) (C.tangentPlaneCell_lipschitz retain v chain covers)
    (C.tangentPlaneCell_cyclic_compatible retain v chain covers closes full)

@[simp] theorem cyclicDevelopment_faceMap {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (closes : C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first)
    (full : (C.linkAngularFan retain v chain).totalAngle = 2 * Real.pi)
    (q : C.CornerAt retain v) (x : C.TangentCell retain v q) :
    C.cyclicDevelopment retain v chain covers closes full (C.tangentFaceMap retain v q x) =
      C.tangentPlaneCell retain v chain covers q x := rfl

theorem cyclicDevelopment_lipschitz {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (closes : C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first)
    (full : (C.linkAngularFan retain v chain).totalAngle = 2 * Real.pi) :
    LipschitzWith 1 (C.cyclicDevelopment retain v chain covers closes full) :=
  MetricGluing.lift_lipschitz (C.TangentCell retain v) (C.tangentGlue retain v)
    (C.tangentPlaneCell retain v chain covers) (C.tangentPlaneCell_lipschitz retain v chain covers)
    (C.tangentPlaneCell_cyclic_compatible retain v chain covers closes full)

theorem cyclicDevelopment_angularToTangent {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (closes : C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first)
    (full : (C.linkAngularFan retain v chain).totalAngle = 2 * Real.pi)
    (z : (C.linkAngularFan retain v chain).Surface) :
    C.cyclicDevelopment retain v chain covers closes full (C.angularToTangent retain v chain z) =
      (C.linkAngularFan retain v chain).develop z := by
  obtain ⟨⟨i, x⟩, rfl⟩ := MetricGluing.point_surjective
    (C.linkAngularFan retain v chain).Cell (C.linkAngularFan retain v chain).glue z
  change C.cyclicDevelopment retain v chain covers closes full
    (C.angularToTangent retain v chain ((C.linkAngularFan retain v chain).faceMap i x)) = _
  rw [C.angularToTangent_faceMap]
  change C.cyclicDevelopment retain v chain covers closes full
    (C.tangentFaceMap retain v (C.linkCornerAt retain v chain i)
      ((C.linkSectorIsometry retain v chain i).symm x)) = _
  rw [C.cyclicDevelopment_faceMap]
  have coordinates := C.linkSectorIsometry_agrees retain v chain i
    ((C.linkSectorIsometry retain v chain i).symm x)
  rw [IsometryEquiv.apply_symm_apply] at coordinates
  exact (C.tangentPlaneCell_of_coordinates retain v chain covers _ _ i x rfl
    coordinates.symm).trans ((C.linkAngularFan retain v chain).develop_faceMap i x).symm

@[simp] theorem cyclicDevelopment_origin {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (closes : C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first)
    (full : (C.linkAngularFan retain v chain).totalAngle = 2 * Real.pi) :
    C.cyclicDevelopment retain v chain covers closes full (C.tangentOrigin retain v) = 0 := by
  rw [← C.angularToTangent_origin retain v chain,
    C.cyclicDevelopment_angularToTangent, AngularFan.develop_origin]

theorem cyclicDevelopment_surjective {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (closes : C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first)
    (full : (C.linkAngularFan retain v chain).totalAngle = 2 * Real.pi) :
    Function.Surjective (C.cyclicDevelopment retain v chain covers closes full) := by
  intro z
  obtain ⟨w, equal⟩ := (C.linkAngularFan retain v chain).develop_surjective_of_full full z
  exact ⟨C.angularToTangent retain v chain w,
    (C.cyclicDevelopment_angularToTangent retain v chain covers closes full w).trans equal⟩

theorem norm_cyclicDevelopment {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (closes : C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first)
    (full : (C.linkAngularFan retain v chain).totalAngle = 2 * Real.pi)
    (z : C.TangentFan retain v) :
    ‖C.cyclicDevelopment retain v chain covers closes full z‖ =
      dist (C.tangentOrigin retain v) z := by
  obtain ⟨w, rfl⟩ := C.angularToTangent_surjective retain v chain covers z
  rw [C.cyclicDevelopment_angularToTangent, AngularFan.norm_develop]
  have radial := congrArg ENNReal.toReal (C.angularToTangent_radial retain v chain w)
  have distances : dist (C.tangentOrigin retain v) (C.angularToTangent retain v chain w) =
      dist (C.linkAngularFan retain v chain).origin w := by
    simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using radial
  exact distances.symm

end Unfoldings.TriangleComplex
