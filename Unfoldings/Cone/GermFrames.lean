module

public import Unfoldings.Cone.CornerDirection
public import Unfoldings.Cone.SeamRadius

/-!
# Rigid coordinates following actual link germs

Every germ supplies an ambient rigid frame whose initial bank lies on the
positive real axis. Actual paired radial banks have the corresponding
initial/terminal coordinates at every prescribed radius.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

def germFrame (p : C.Germ) : Plane ≃ᵃⁱ[ℝ] ℂ :=
  ((C.triangle p.1.1).cornerFrame p.1.2).directedPlace p.2

theorem germFrame_initial (p : C.Germ)
    (x : (C.triangle p.1.1).cornerWedge p.1.2)
    (bank : (C.triangle p.1.1).bankCoord p.1.2 p.2 x.val = 0) :
    C.germFrame p x.val = (dist ((C.triangle p.1.1).vertex p.1.2) x.val : ℂ) := by
  have boundary : if p.2 then (C.triangle p.1.1).coord (Triangle.next p.1.2) x.val = 0
      else (C.triangle p.1.1).coord (Triangle.next (Triangle.next p.1.2)) x.val = 0 := by
    cases side : p.2 <;> simpa [Triangle.bankCoord, side] using bank
  have equal := ((C.triangle p.1.1).cornerFrame p.1.2).directed_initial_radius p.2 x boundary
  rw [Triangle.CornerFrame.directedSectorIsometry_agrees] at equal
  exact equal

theorem germFrame_terminal (p : C.Germ)
    (x : (C.triangle p.1.1).cornerWedge p.1.2)
    (bank : (C.triangle p.1.1).bankCoord p.1.2 (!p.2) x.val = 0) :
    C.germFrame p x.val = dist ((C.triangle p.1.1).vertex p.1.2) x.val •
      polarRay ((C.triangle p.1.1).cornerAngle p.1.2) := by
  have boundary : if p.2 then
      (C.triangle p.1.1).coord (Triangle.next (Triangle.next p.1.2)) x.val = 0
      else (C.triangle p.1.1).coord (Triangle.next p.1.2) x.val = 0 := by
    cases side : p.2 <;> simpa [Triangle.bankCoord, side] using bank
  have equal := ((C.triangle p.1.1).cornerFrame p.1.2).directed_terminal_radius p.2 x boundary
  rw [Triangle.CornerFrame.directedSectorIsometry_agrees] at equal
  exact equal

variable (retain : Set C.Seam) (v : C.Vertex retain)

abbrev tangentSourceGerm (s : C.TangentSeam retain v) : C.Germ :=
  C.germOfEndpoint (C.seamSide s.val.1 s.val.2.1) s.val.2.2

abbrev tangentTargetGerm (s : C.TangentSeam retain v) : C.Germ :=
  C.germOfEndpoint (C.seamSide s.val.1 (!s.val.2.1))
    (C.acrossEndpoint s.val.1 s.val.2.1 s.val.2.2)

/-- The source corner is entered on its other bank, so this seam is terminal in its frame. -/
theorem germFrame_seam_left (s : C.TangentSeam retain v) (r : ℝ≥0) :
    C.germFrame (C.turnGerm (C.tangentSourceGerm retain v s))
      (C.tangentSeamPointLeft retain v s r).val =
      (r : ℝ) • polarRay ((C.triangle (C.tangentLeft retain v s).val.1).cornerAngle
        (C.tangentLeft retain v s).val.2) := by
  have bank := C.tangentLeftPoint_bankCoord retain v s
    (C.tangentSeamOtherEndpoint retain v s) ((r : ℝ) / C.tangentSeamLength retain v s)
    (div_nonneg r.coe_nonneg (C.tangentSeamLength_pos retain v s).le)
  have bound := C.germFrame_terminal (C.turnGerm (C.tangentSourceGerm retain v s))
    (C.tangentSeamPointLeft retain v s r) (by
      change (C.triangle (C.tangentLeft retain v s).val.1).bankCoord
        (C.tangentLeft retain v s).val.2 (!!s.val.2.2)
          (C.tangentSeamPointLeft retain v s r).val = 0
      rw [Bool.not_not]
      exact bank)
  have radius := C.tangentSeamPointLeft_radius retain v s r
  change dist ((C.triangle (C.tangentLeft retain v s).val.1).vertex
    (C.tangentLeft retain v s).val.2) (C.tangentSeamPointLeft retain v s r).val = (r : ℝ) at radius
  change C.germFrame (C.turnGerm (C.tangentSourceGerm retain v s))
    (C.tangentSeamPointLeft retain v s r).val =
      dist ((C.triangle (C.tangentLeft retain v s).val.1).vertex
        (C.tangentLeft retain v s).val.2) (C.tangentSeamPointLeft retain v s r).val •
          polarRay ((C.triangle (C.tangentLeft retain v s).val.1).cornerAngle
            (C.tangentLeft retain v s).val.2) at bound
  rwa [radius] at bound

theorem germFrame_seam_right (s : C.TangentSeam retain v) (r : ℝ≥0) :
    C.germFrame (C.tangentTargetGerm retain v s)
      (C.tangentSeamPointRight retain v s r).val = (r : ℂ) := by
  have bank := C.tangentRightPoint_bankCoord retain v s
    (C.tangentSeamOtherEndpoint retain v s) ((r : ℝ) / C.tangentSeamLength retain v s)
    (div_nonneg r.coe_nonneg (C.tangentSeamLength_pos retain v s).le)
  have bound := C.germFrame_initial (C.tangentTargetGerm retain v s)
    (C.tangentSeamPointRight retain v s r) bank
  have radius := C.tangentSeamPointRight_radius retain v s r
  change dist ((C.triangle (C.tangentRight retain v s).val.1).vertex
    (C.tangentRight retain v s).val.2)
      (C.tangentSeamPointRight retain v s r).val = (r : ℝ) at radius
  change C.germFrame (C.tangentTargetGerm retain v s)
    (C.tangentSeamPointRight retain v s r).val =
      (dist ((C.triangle (C.tangentRight retain v s).val.1).vertex
        (C.tangentRight retain v s).val.2) (C.tangentSeamPointRight retain v s r).val : ℂ) at bound
  rwa [radius] at bound

end Unfoldings.TriangleComplex
