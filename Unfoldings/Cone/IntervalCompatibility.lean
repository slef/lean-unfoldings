module

public import Unfoldings.Cone.TangentAngularCells
public import Unfoldings.Cone.IntervalSeams
public import Unfoldings.Cone.SeamCoordinates

/-!
# Actual seam compatibility of the inverse interval comparison

Every radial seam is consecutive in the interval link order. Its directed
coordinates are the two equal-radius angular banks, so the original tagged
cell maps agree after gluing them into the angular realization.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

theorem tangentCellToAngular_consecutive {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (k : Fin n) (r : ℝ≥0)
    (a b : C.CornerAt retain v) (x : C.TangentCell retain v a) (y : C.TangentCell retain v b)
    (left_corner : a.val = (chain.point k.castSucc).val.1)
    (right_corner : b.val = (chain.point k.succ).val.1)
    (left_coordinates : C.germFrame (chain.point k.castSucc).val x.val =
      (r : ℝ) • polarRay ((C.linkAngularFan retain v chain).angle k.castSucc))
    (right_coordinates : C.germFrame (chain.point k.succ).val y.val = (r : ℂ)) :
    C.tangentCellToAngular retain v chain covers a x =
      C.tangentCellToAngular retain v chain covers b y := by
  calc
    _ = (C.linkAngularFan retain v chain).faceMap k.castSucc
        ((C.linkAngularFan retain v chain).finish k.castSucc r) :=
      C.tangentCellToAngular_of_coordinates retain v chain covers a x _ _ left_corner
        left_coordinates
    _ = (C.linkAngularFan retain v chain).faceMap k.succ
        ((C.linkAngularFan retain v chain).start k.succ r) :=
      MetricGluing.point_eq_of_glue (C.linkAngularFan retain v chain).Cell ⟨k, r, rfl, rfl⟩
    _ = _ := (C.tangentCellToAngular_of_coordinates retain v chain covers b y _ _
      right_corner right_coordinates).symm

theorem tangentCellToAngular_interval_compatible {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (start : C.linkMate retain v chain.first = chain.first)
    (finish : C.linkMate retain v (C.linkTurn retain v chain.last) =
      C.linkTurn retain v chain.last)
    (a b : MetricGluing.Total (C.TangentCell retain v))
    (joined : C.tangentGlue retain v a b) :
    C.tangentCellToAngular retain v chain covers a.1 a.2 =
      C.tangentCellToAngular retain v chain covers b.1 b.2 := by
  obtain ⟨s, x, t, nonnegative, rfl, rfl⟩ := joined
  let r : ℝ≥0 := ⟨dist (C.tangentApex retain v (C.tangentLeft retain v s))
    (C.tangentLeftPoint retain v s x t nonnegative), dist_nonneg⟩
  rcases C.tangentSeam_interval_cases retain v chain covers start finish s with
    ⟨k, source, target⟩ | ⟨k, source, target⟩
  · have left_corner : (C.tangentLeft retain v s).val = (chain.point k.castSucc).val.1 := by
      have corners := congrArg (fun p : C.Germ => p.1) source
      exact corners
    have right_corner : (C.tangentRight retain v s).val = (chain.point k.succ).val.1 :=
      congrArg Prod.fst target
    have turned : C.turnGerm (C.tangentSourceGerm retain v s) = (chain.point k.castSucc).val :=
      (congrArg C.turnGerm source).trans (C.turnGerm_involutive _)
    have angle := congrArg (fun c : C.Corner => (C.triangle c.1).cornerAngle c.2) left_corner
    change (C.triangle (C.tangentLeft retain v s).val.1).cornerAngle
      (C.tangentLeft retain v s).val.2 = (C.linkAngularFan retain v chain).angle k.castSucc at angle
    have left_coordinates := C.germFrame_radial_left retain v s x t nonnegative
    rw [turned, angle] at left_coordinates
    have right_coordinates := C.germFrame_radial_right retain v s x t nonnegative
    rw [target, ← C.tangentRadialSeam_radius_eq retain v s x t nonnegative] at right_coordinates
    exact C.tangentCellToAngular_consecutive retain v chain covers k r _ _ _ _
      left_corner right_corner left_coordinates right_coordinates
  · have left_corner : (C.tangentRight retain v s).val = (chain.point k.castSucc).val.1 := by
      have corners := congrArg (fun p : C.Germ => p.1) target
      exact corners
    have right_corner : (C.tangentLeft retain v s).val = (chain.point k.succ).val.1 :=
      congrArg Prod.fst source
    have turned : C.turnGerm (C.tangentTargetGerm retain v s) =
        (chain.point k.castSucc).val :=
      (congrArg C.turnGerm target).trans (C.turnGerm_involutive _)
    have angle := congrArg (fun c : C.Corner => (C.triangle c.1).cornerAngle c.2) left_corner
    change (C.triangle (C.tangentRight retain v s).val.1).cornerAngle
      (C.tangentRight retain v s).val.2 =
        (C.linkAngularFan retain v chain).angle k.castSucc at angle
    have left_coordinates := C.germFrame_radial_right_terminal retain v s x t nonnegative
    rw [turned, angle, ← C.tangentRadialSeam_radius_eq retain v s x t nonnegative]
      at left_coordinates
    have right_coordinates := C.germFrame_radial_left_initial retain v s x t nonnegative
    rw [source] at right_coordinates
    exact (C.tangentCellToAngular_consecutive retain v chain covers k r _ _ _ _
      left_corner right_corner left_coordinates right_coordinates).symm

end Unfoldings.TriangleComplex
