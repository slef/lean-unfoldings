module

public import Unfoldings.Cone.GermFrames

/-!
# Directed coordinates on every actual radial seam point

The earlier prescribed-radius witnesses are not needed here: every radial
extension of every original edge point has the correct initial/terminal
coordinates, with the same radius on both wedges.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

theorem germFrame_radial_left_initial (s : C.TangentSeam retain v)
    (x : C.TangentDomain retain v s) (t : ℝ) (nonnegative : 0 ≤ t) :
    C.germFrame (C.tangentSourceGerm retain v s)
      (C.tangentLeftPoint retain v s x t nonnegative).val =
      (dist (C.tangentApex retain v (C.tangentLeft retain v s))
        (C.tangentLeftPoint retain v s x t nonnegative) : ℂ) :=
  C.germFrame_initial (C.tangentSourceGerm retain v s)
    (C.tangentLeftPoint retain v s x t nonnegative)
    (C.tangentLeftPoint_bankCoord retain v s x t nonnegative)

theorem germFrame_radial_left (s : C.TangentSeam retain v)
    (x : C.TangentDomain retain v s) (t : ℝ) (nonnegative : 0 ≤ t) :
    C.germFrame (C.turnGerm (C.tangentSourceGerm retain v s))
      (C.tangentLeftPoint retain v s x t nonnegative).val =
      dist (C.tangentApex retain v (C.tangentLeft retain v s))
        (C.tangentLeftPoint retain v s x t nonnegative) •
          polarRay ((C.triangle (C.tangentLeft retain v s).val.1).cornerAngle
            (C.tangentLeft retain v s).val.2) := by
  apply C.germFrame_terminal
  change (C.triangle (C.tangentLeft retain v s).val.1).bankCoord
    (C.tangentLeft retain v s).val.2 (!!s.val.2.2)
      (C.tangentLeftPoint retain v s x t nonnegative).val = 0
  rw [Bool.not_not]
  exact C.tangentLeftPoint_bankCoord retain v s x t nonnegative

theorem germFrame_radial_right (s : C.TangentSeam retain v)
    (x : C.TangentDomain retain v s) (t : ℝ) (nonnegative : 0 ≤ t) :
    C.germFrame (C.tangentTargetGerm retain v s)
      (C.tangentRightPoint retain v s x t nonnegative).val =
      (dist (C.tangentApex retain v (C.tangentRight retain v s))
        (C.tangentRightPoint retain v s x t nonnegative) : ℂ) := by
  exact C.germFrame_initial (C.tangentTargetGerm retain v s)
    (C.tangentRightPoint retain v s x t nonnegative)
    (C.tangentRightPoint_bankCoord retain v s x t nonnegative)

theorem germFrame_radial_right_terminal (s : C.TangentSeam retain v)
    (x : C.TangentDomain retain v s) (t : ℝ) (nonnegative : 0 ≤ t) :
    C.germFrame (C.turnGerm (C.tangentTargetGerm retain v s))
      (C.tangentRightPoint retain v s x t nonnegative).val =
      dist (C.tangentApex retain v (C.tangentRight retain v s))
        (C.tangentRightPoint retain v s x t nonnegative) •
          polarRay ((C.triangle (C.tangentRight retain v s).val.1).cornerAngle
            (C.tangentRight retain v s).val.2) := by
  apply C.germFrame_terminal
  change (C.triangle (C.tangentRight retain v s).val.1).bankCoord
    (C.tangentRight retain v s).val.2
      (!!C.acrossEndpoint s.val.1 s.val.2.1 s.val.2.2)
        (C.tangentRightPoint retain v s x t nonnegative).val = 0
  rw [Bool.not_not]
  exact C.tangentRightPoint_bankCoord retain v s x t nonnegative

theorem tangentRadialSeam_radius_eq (s : C.TangentSeam retain v)
    (x : C.TangentDomain retain v s) (t : ℝ) (nonnegative : 0 ≤ t) :
    dist (C.tangentApex retain v (C.tangentLeft retain v s))
      (C.tangentLeftPoint retain v s x t nonnegative) =
    dist (C.tangentApex retain v (C.tangentRight retain v s))
      (C.tangentRightPoint retain v s x t nonnegative) := by
  have equal := C.tangentCellRadius_compatible retain v _ _
    ⟨s, x, t, nonnegative, rfl, rfl⟩
  change dist (C.tangentLeftPoint retain v s x t nonnegative)
      (C.tangentApex retain v (C.tangentLeft retain v s)) =
    dist (C.tangentRightPoint retain v s x t nonnegative)
      (C.tangentApex retain v (C.tangentRight retain v s)) at equal
  rwa [dist_comm (C.tangentLeftPoint retain v s x t nonnegative),
    dist_comm (C.tangentRightPoint retain v s x t nonnegative)] at equal

end Unfoldings.TriangleComplex
