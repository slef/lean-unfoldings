module

public import Unfoldings.Cone.GermFrames
public import Unfoldings.Cone.LinkAngles
public import Unfoldings.Cone.AngularMetric

/-!
# Comparing ordered angular fans with actual tangent fans

Each angular sector maps back through the rigid frame following its actual
initial germ. Consecutive angular ray identifications are actual radial seam
identifications at the same radius. Thus the comparison descends through the
constructed route metrics, without any spatial-folding hypothesis.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

theorem exists_tangentSeam_of_link_next_germs (p q : C.LinkGerm retain v)
    (next : C.linkMate retain v (C.linkTurn retain v p) = q)
    (different : q ≠ C.linkTurn retain v p) :
    ∃ s : C.TangentSeam retain v,
      C.tangentSourceGerm retain v s = C.turnGerm p.val ∧
      C.tangentTargetGerm retain v s = q.val := by
  have moved : C.mateGerm retain (C.turnGerm p.val) ≠ C.turnGerm p.val := by
    intro fixed
    exact different (next.symm.trans (Subtype.ext fixed))
  have crossing := C.germCrosses_mate_of_ne retain (C.turnGerm p.val) moved
  have target : C.mateGerm retain (C.turnGerm p.val) = q.val := congrArg Subtype.val next
  rw [target] at crossing
  obtain ⟨s, kept, side, b, source, target⟩ := crossing
  have vertex : C.vertexOfCorner retain
      (C.germOfEndpoint (C.seamSide s side) b).1 = v := by
    rw [← source]
    exact p.property
  exact ⟨⟨(s, side, b), kept, vertex⟩, source.symm, target.symm⟩

def linkCornerAt {n : ℕ} (chain : (C.linkSystem retain v).Chain n) (i : Fin (n + 1)) :
    C.CornerAt retain v := ⟨(chain.point i).val.1, (chain.point i).property⟩

def linkSectorIsometry {n : ℕ} (chain : (C.linkSystem retain v).Chain n) (i : Fin (n + 1)) :
    C.TangentCell retain v (C.linkCornerAt retain v chain i) ≃ᵢ
      (C.linkAngularFan retain v chain).Cell i :=
  ((C.triangle (chain.point i).val.1.1).cornerFrame (chain.point i).val.1.2).directedSectorIsometry
    (chain.point i).val.2

theorem linkSectorIsometry_agrees {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (i : Fin (n + 1)) (x : C.TangentCell retain v (C.linkCornerAt retain v chain i)) :
    (C.linkSectorIsometry retain v chain i x).val = C.germFrame (chain.point i).val x.val :=
  Triangle.CornerFrame.directedSectorIsometry_agrees _ _ x

def linkCellToTangent {n : ℕ} (chain : (C.linkSystem retain v).Chain n) (i : Fin (n + 1))
    (x : (C.linkAngularFan retain v chain).Cell i) : C.TangentFan retain v :=
  C.tangentFaceMap retain v (C.linkCornerAt retain v chain i)
    ((C.linkSectorIsometry retain v chain i).symm x)

theorem linkCellToTangent_lipschitz {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (i : Fin (n + 1)) : LipschitzWith 1 (C.linkCellToTangent retain v chain i) := by
  change LipschitzWith 1
    (C.tangentFaceMap retain v (C.linkCornerAt retain v chain i) ∘
      (C.linkSectorIsometry retain v chain i).symm)
  simpa only [one_mul] using
    (C.tangentFaceMap_lipschitz retain v (C.linkCornerAt retain v chain i)).comp
      (C.linkSectorIsometry retain v chain i).symm.isometry.lipschitzWith

theorem linkCellToTangent_of_coordinates {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (i : Fin (n + 1))
    (x : (C.linkAngularFan retain v chain).Cell i)
    (q : C.CornerAt retain v) (y : C.TangentCell retain v q)
    (corner : q.val = (chain.point i).val.1)
    (coordinates : C.germFrame (chain.point i).val y.val = x.val) :
    C.linkCellToTangent retain v chain i x = C.tangentFaceMap retain v q y := by
  have same : q = C.linkCornerAt retain v chain i := Subtype.ext corner
  subst q
  apply congrArg (C.tangentFaceMap retain v (C.linkCornerAt retain v chain i))
  apply (C.linkSectorIsometry retain v chain i).injective
  rw [IsometryEquiv.apply_symm_apply]
  apply Subtype.ext
  exact ((C.linkSectorIsometry_agrees retain v chain i y).trans coordinates).symm

theorem linkCellToTangent_joined {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (i : Fin n) (r : ℝ≥0) :
    C.linkCellToTangent retain v chain i.castSucc
      ((C.linkAngularFan retain v chain).finish i.castSucc r) =
    C.linkCellToTangent retain v chain i.succ
      ((C.linkAngularFan retain v chain).start i.succ r) := by
  obtain ⟨s, source, target⟩ := C.exists_tangentSeam_of_link_next_germs retain v
    (chain.point i.castSucc) (chain.point i.succ) (chain.next i)
    (chain.disjoint i.succ i.castSucc)
  have source_corner : (C.tangentLeft retain v s).val = (chain.point i.castSucc).val.1 := by
    have corners := congrArg (fun p : C.Germ => p.1) source
    exact corners
  have target_corner : (C.tangentRight retain v s).val = (chain.point i.succ).val.1 :=
    congrArg Prod.fst target
  have turned : C.turnGerm (C.tangentSourceGerm retain v s) = (chain.point i.castSucc).val :=
    (congrArg C.turnGerm source).trans (C.turnGerm_involutive _)
  have left_coordinates := C.germFrame_seam_left retain v s r
  rw [turned] at left_coordinates
  have angle := congrArg (fun c : C.Corner => (C.triangle c.1).cornerAngle c.2) source_corner
  change (C.triangle (C.tangentLeft retain v s).val.1).cornerAngle
    (C.tangentLeft retain v s).val.2 = (C.linkAngularFan retain v chain).angle i.castSucc at angle
  rw [angle] at left_coordinates
  have right_coordinates := C.germFrame_seam_right retain v s r
  rw [target] at right_coordinates
  calc
    _ = C.tangentFaceMap retain v (C.tangentLeft retain v s)
        (C.tangentSeamPointLeft retain v s r) :=
      C.linkCellToTangent_of_coordinates retain v chain i.castSucc _ _
        (C.tangentSeamPointLeft retain v s r) source_corner left_coordinates
    _ = C.tangentFaceMap retain v (C.tangentRight retain v s)
        (C.tangentSeamPointRight retain v s r) :=
      MetricGluing.point_eq_of_glue (C.TangentCell retain v)
        (C.tangentSeamPoints_glue retain v s r)
    _ = _ := (C.linkCellToTangent_of_coordinates retain v chain i.succ _ _
      (C.tangentSeamPointRight retain v s r) target_corner right_coordinates).symm

theorem linkCellToTangent_compatible {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (a b : MetricGluing.Total (C.linkAngularFan retain v chain).Cell)
    (joined : (C.linkAngularFan retain v chain).glue a b) :
    C.linkCellToTangent retain v chain a.1 a.2 = C.linkCellToTangent retain v chain b.1 b.2 := by
  obtain ⟨i, r, rfl, rfl⟩ := joined
  exact C.linkCellToTangent_joined retain v chain i r

/-- Restoring a possible final slit is a constructed nonexpanding metric map. -/
def angularToTangent {n : ℕ} (chain : (C.linkSystem retain v).Chain n) :
    (C.linkAngularFan retain v chain).Surface → C.TangentFan retain v :=
  MetricGluing.lift (C.linkAngularFan retain v chain).Cell (C.linkAngularFan retain v chain).glue
    (C.linkCellToTangent retain v chain) (C.linkCellToTangent_lipschitz retain v chain)
    (C.linkCellToTangent_compatible retain v chain)

@[simp] theorem angularToTangent_faceMap {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (i : Fin (n + 1)) (x : (C.linkAngularFan retain v chain).Cell i) :
    C.angularToTangent retain v chain ((C.linkAngularFan retain v chain).faceMap i x) =
      C.linkCellToTangent retain v chain i x := rfl

theorem angularToTangent_lipschitz {n : ℕ} (chain : (C.linkSystem retain v).Chain n) :
    LipschitzWith 1 (C.angularToTangent retain v chain) :=
  MetricGluing.lift_lipschitz (C.linkAngularFan retain v chain).Cell
    (C.linkAngularFan retain v chain).glue (C.linkCellToTangent retain v chain)
    (C.linkCellToTangent_lipschitz retain v chain) (C.linkCellToTangent_compatible retain v chain)

/-- Every original tangent point occurs in the ordered angular model when the chain covers. -/
theorem angularToTangent_surjective {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (covers : ∀ p, chain.Visited p) : Function.Surjective (C.angularToTangent retain v chain) := by
  intro z
  obtain ⟨⟨q, y⟩, rfl⟩ := MetricGluing.point_surjective
    (C.TangentCell retain v) (C.tangentGlue retain v) z
  obtain ⟨i, index⟩ := (C.linkCornerEquiv retain v chain covers).surjective q
  have same : q = C.linkCornerAt retain v chain i := index.symm
  clear index
  subst q
  refine ⟨(C.linkAngularFan retain v chain).faceMap i
    (C.linkSectorIsometry retain v chain i y), ?_⟩
  rw [C.angularToTangent_faceMap]
  change C.tangentFaceMap retain v (C.linkCornerAt retain v chain i)
    ((C.linkSectorIsometry retain v chain i).symm
      (C.linkSectorIsometry retain v chain i y)) = _
  rw [IsometryEquiv.symm_apply_apply]
  rfl

theorem linkCellToTangent_radial {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (i : Fin (n + 1)) (x : (C.linkAngularFan retain v chain).Cell i) :
    edist (C.tangentOrigin retain v) (C.linkCellToTangent retain v chain i x) =
      edist (0 : ℂ) x.val := by
  let iso := C.linkSectorIsometry retain v chain i
  let apex := C.tangentApex retain v (C.linkCornerAt retain v chain i)
  have zero : (iso apex).val = 0 :=
    Triangle.CornerFrame.directedSectorIsometry_apex _ _
  have equal := iso.isometry.edist_eq apex (iso.symm x)
  rw [IsometryEquiv.apply_symm_apply] at equal
  change edist (iso apex).val x.val = edist apex (iso.symm x) at equal
  rw [zero] at equal
  change edist (C.tangentOrigin retain v)
    (C.tangentFaceMap retain v (C.linkCornerAt retain v chain i) (iso.symm x)) = _
  rw [C.tangent_edist_origin_faceMap]
  exact equal.symm

/-- Restoring the possible final slit preserves every distance from the common apex. -/
theorem angularToTangent_radial {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (z : (C.linkAngularFan retain v chain).Surface) :
    edist (C.tangentOrigin retain v) (C.angularToTangent retain v chain z) =
      edist (C.linkAngularFan retain v chain).origin z := by
  obtain ⟨⟨i, x⟩, rfl⟩ := MetricGluing.point_surjective
    (C.linkAngularFan retain v chain).Cell (C.linkAngularFan retain v chain).glue z
  change edist (C.tangentOrigin retain v)
    (C.angularToTangent retain v chain ((C.linkAngularFan retain v chain).faceMap i x)) = _
  rw [C.angularToTangent_faceMap, C.linkCellToTangent_radial]
  exact ((C.linkAngularFan retain v chain).edist_origin_faceMap i x).symm

@[simp] theorem angularToTangent_origin {n : ℕ} (chain : (C.linkSystem retain v).Chain n) :
    C.angularToTangent retain v chain (C.linkAngularFan retain v chain).origin =
      C.tangentOrigin retain v := by
  apply (edist_eq_zero.mp _).symm
  rw [C.angularToTangent_radial, edist_self]

end Unfoldings.TriangleComplex
