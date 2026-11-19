module

public import Unfoldings.Cone.IntervalSector
public import Unfoldings.Cone.TriangleInclusion
public import Unfoldings.Complex.DirectedBoundaryPath
public import Unfoldings.Complex.BoundaryRolling

/-! Angular coordinates of the original directed banks in a retained interval fan. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (w : C.Vertex retain)

/-- The record of a directed bank point in its original triangular face. -/
def directedBankCell (p : C.BoundaryEnd retain) (t : unitInterval) : C.Cell p.val.1.1 :=
  let bank := (C.boundaryEndEquiv retain p).1
  (C.triangle p.val.1.1).edgeMap bank.val.edge (C.bankParameterFromEnd bank p.val.2 t)

private theorem directedBankCell_coord (p : C.BoundaryEnd retain) (t : unitInterval) :
    (C.triangle p.val.1.1).bankCoord p.val.1.2 p.val.2 (C.directedBankCell retain p t).val = 0 := by
  obtain ⟨⟨bank, b⟩, rfl⟩ := (C.boundaryEndEquiv retain).symm.surjective p
  let e := bank.val.edge
  let T := C.triangle bank.val.face
  have zero := T.coord_edge_eq_zero e (C.bankParameterFromEnd bank b t)
  obtain ⟨⟨f, i⟩, property⟩ := bank
  cases b <;> fin_cases i <;> exact zero

private theorem directedBankCell_radius (p : C.BoundaryEnd retain) (t : unitInterval) :
    dist ((C.triangle p.val.1.1).vertex p.val.1.2) (C.directedBankCell retain p t).val =
      t.val * C.boundaryBankLength p := by
  have calculate (f : Face) (i j : Fin 3) :
      dist ((C.triangle f).vertex i)
          (AffineMap.lineMap ((C.triangle f).vertex i) ((C.triangle f).vertex j) t.val) =
        t.val * dist ((C.triangle f).vertex j) ((C.triangle f).vertex i) := by
    rw [dist_comm ((C.triangle f).vertex i), dist_eq_norm, AffineMap.lineMap_apply_module',
      add_sub_cancel_right, norm_smul, Real.norm_of_nonneg t.property.1, dist_eq_norm]
  obtain ⟨⟨⟨f, i⟩, b⟩, bound⟩ := p
  cases b <;> fin_cases i <;> exact calculate f _ _

/-- The original directed bank point as a tagged point of its supporting tangent wedge. -/
def directedBankTangentTag (p : C.BoundaryEnd retain) (at_vertex : C.boundaryEndVertex retain p = w)
    (t : unitInterval) : C.TangentTotal retain w :=
  ⟨⟨p.val.1, at_vertex⟩, C.tangentInclude retain w ⟨p.val.1, at_vertex⟩
    (C.directedBankCell retain p t)⟩

@[simp] theorem tangentSurfaceTag_directedBankTangentTag (p : C.BoundaryEnd retain)
    (at_vertex : C.boundaryEndVertex retain p = w) (t : unitInterval) :
    C.tangentSurfaceTag retain w (C.directedBankTangentTag retain w p at_vertex t) =
      C.directedBoundaryPath p t :=
  C.tangentSurfaceTag_of_mem retain w _ (C.directedBankCell retain p t).property

theorem edist_tangentPoint_directedBankTangentTag (p : C.BoundaryEnd retain)
    (at_vertex : C.boundaryEndVertex retain p = w) (t : unitInterval) :
    edist (C.tangentPoint retain w (C.directedBankTangentTag retain w p at_vertex t))
      (C.tangentOrigin retain w) = ENNReal.ofReal (t.val * C.boundaryBankLength p) := by
  rw [edist_comm]
  let a := C.directedBankTangentTag retain w p at_vertex t
  exact (C.tangent_edist_origin_faceMap retain w a.1 a.2).trans
    ((edist_dist _ _).trans (congrArg ENNReal.ofReal (C.directedBankCell_radius retain p t)))

open scoped NNReal

variable {n : ℕ} (c : (C.linkSystem retain w).Chain n) (covers : ∀ p, c.Visited p)
  (start : C.linkMate retain w c.first = c.first)
  (finish : C.linkMate retain w (C.linkTurn retain w c.last) = C.linkTurn retain w c.last)
  (small : C.totalAngle retain w < 2 * Real.pi)

local notation "Iso" => C.intervalSectorIsometryEquiv retain w c covers start finish small

private theorem intervalSector_directedBankTangentTag_at (i : Fin (n + 1))
    (p : C.BoundaryEnd retain) (at_vertex : C.boundaryEndVertex retain p = w)
    (corner : p.val.1 = (c.point i).val.1) (t : unitInterval)
    (x : (C.linkAngularFan retain w c).Cell i)
    (frame : C.germFrame (c.point i).val (C.directedBankCell retain p t).val = x.val) :
    (Iso (C.tangentPoint retain w (C.directedBankTangentTag retain w p at_vertex t))).val =
      (C.linkAngularFan retain w c).place i x := by
  have equal := C.linkCellToTangent_of_coordinates retain w c i x ⟨p.val.1, at_vertex⟩
    (C.tangentInclude retain w ⟨p.val.1, at_vertex⟩ (C.directedBankCell retain p t)) corner frame
  rw [show C.tangentPoint retain w (C.directedBankTangentTag retain w p at_vertex t) =
      C.linkCellToTangent retain w c i x from equal.symm, ← C.angularToTangent_faceMap,
    C.intervalSectorIsometryEquiv_angularToTangent, AngularFan.develop_faceMap]

/-- The first literal directed bank has its original arclength on the positive axis. -/
theorem intervalSector_directedBankTangentTag_first
    (p : C.BoundaryEnd retain) (at_vertex : C.boundaryEndVertex retain p = w)
    (first : c.first.val = p.val) (t : unitInterval) :
    (Iso (C.tangentPoint retain w (C.directedBankTangentTag retain w p at_vertex t))).val =
      (t.val * C.boundaryBankLength p : ℝ) := by
  let A := C.linkAngularFan retain w c
  let r : ℝ≥0 := ⟨t.val * C.boundaryBankLength p,
    mul_nonneg t.property.1 (C.boundaryBankLength_pos p).le⟩
  have coordinates : C.germFrame (c.point 0).val (C.directedBankCell retain p t).val =
      (A.start 0 r).val := by
    change C.germFrame c.first.val _ = _
    rw [first]
    have image := C.germFrame_initial p.val
      (C.tangentInclude retain w ⟨p.val.1, at_vertex⟩ (C.directedBankCell retain p t))
      (C.directedBankCell_coord retain p t)
    change C.germFrame p.val (C.directedBankCell retain p t).val = _ at image
    exact image.trans (congrArg (fun a : ℝ => (a : ℂ)) (C.directedBankCell_radius retain p t))
  rw [C.intervalSector_directedBankTangentTag_at retain w c covers start finish small 0 p
    at_vertex (congrArg Prod.fst first.symm) t (A.start 0 r) coordinates, A.place_start]
  rw [show (0 : Fin (n + 1)).castSucc = 0 from rfl, A.heading_zero, polarRay_zero, mul_one]
  rfl

/-- The last literal directed bank has the same arclength on the terminal ray. -/
theorem intervalSector_directedBankTangentTag_last
    (p : C.BoundaryEnd retain) (at_vertex : C.boundaryEndVertex retain p = w)
    (last : (C.linkTurn retain w c.last).val = p.val) (t : unitInterval) :
    (Iso (C.tangentPoint retain w (C.directedBankTangentTag retain w p at_vertex t))).val =
      (t.val * C.boundaryBankLength p) • polarRay (C.totalAngle retain w) := by
  let A := C.linkAngularFan retain w c
  let r : ℝ≥0 := ⟨t.val * C.boundaryBankLength p,
    mul_nonneg t.property.1 (C.boundaryBankLength_pos p).le⟩
  have turned : C.turnGerm c.last.val = p.val := last
  have previous : c.last.val = C.turnGerm p.val :=
    ((C.turnGerm_involutive c.last.val).symm).trans (congrArg C.turnGerm turned)
  have coordinates : C.germFrame (c.point (Fin.last n)).val (C.directedBankCell retain p t).val =
      (A.finish (Fin.last n) r).val := by
    change C.germFrame c.last.val _ = _
    rw [previous]
    have image := C.germFrame_terminal (C.turnGerm p.val)
      (C.tangentInclude retain w ⟨p.val.1, at_vertex⟩ (C.directedBankCell retain p t)) (by
        change (C.triangle p.val.1.1).bankCoord p.val.1.2 (!!p.val.2)
          (C.directedBankCell retain p t).val = 0
        rw [Bool.not_not]
        exact C.directedBankCell_coord retain p t)
    change C.germFrame (C.turnGerm p.val) (C.directedBankCell retain p t).val =
      dist ((C.triangle p.val.1.1).vertex p.val.1.2) (C.directedBankCell retain p t).val •
        polarRay _ at image
    rw [image, C.directedBankCell_radius retain p t]
    have same_angle : A.angle (Fin.last n) = (C.triangle p.val.1.1).cornerAngle p.val.1.2 := by
      change (C.triangle (C.turnGerm c.last.val).1.1).cornerAngle
        (C.turnGerm c.last.val).1.2 = _
      rw [turned]
    change _ = (r : ℝ) • polarRay (A.angle (Fin.last n))
    rw [same_angle]
    rfl
  have corner : p.val.1 = (c.point (Fin.last n)).val.1 := by
    change p.val.1 = c.last.val.1
    rw [previous]
    rfl
  rw [C.intervalSector_directedBankTangentTag_at retain w c covers start finish small
    (Fin.last n) p at_vertex corner t (A.finish (Fin.last n) r) coordinates,
    A.place_finish, Fin.succ_last, A.heading_last, C.linkAngularFan_totalAngle retain w c covers]
  exact Complex.real_smul.symm

end Unfoldings.TriangleComplex
