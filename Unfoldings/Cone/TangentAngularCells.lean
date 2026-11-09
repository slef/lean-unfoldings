module

public import Unfoldings.Cone.LinkComparison

/-!
# Original tangent cells in their selected angular pieces

A covering link order selects the unique ordinal for each actual corner.
Its directed rigid frame supplies a nonexpanding map of that entire tangent
cell into the angular realization. Compatibility across actual seams is
proved separately for interval and cyclic link orders.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

theorem germFrame_mapsTo (p : C.Germ) :
    Set.MapsTo (C.germFrame p) ((C.triangle p.1.1).cornerWedge p.1.2)
      (planarSector ((C.triangle p.1.1).cornerAngle p.1.2)) := by
  intro x inside
  let frame := (C.triangle p.1.1).cornerFrame p.1.2
  have member := (frame.directedSectorIsometry p.2 ⟨x, inside⟩).property
  rw [frame.directedSectorIsometry_agrees] at member
  exact member

variable (retain : Set C.Seam) (v : C.Vertex retain)

def linkCornerIndex {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (covers : ∀ p, chain.Visited p) (q : C.CornerAt retain v) : Fin (n + 1) :=
  (C.linkCornerEquiv retain v chain covers).symm q

theorem linkCornerIndex_spec {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (covers : ∀ p, chain.Visited p) (q : C.CornerAt retain v) :
    C.linkCornerAt retain v chain (C.linkCornerIndex retain v chain covers q) = q :=
  (C.linkCornerEquiv retain v chain covers).apply_symm_apply q

def tangentSectorPoint {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (covers : ∀ p, chain.Visited p) (q : C.CornerAt retain v) (x : C.TangentCell retain v q) :
    (C.linkAngularFan retain v chain).Cell (C.linkCornerIndex retain v chain covers q) :=
  ⟨C.germFrame (chain.point (C.linkCornerIndex retain v chain covers q)).val x.val, by
    apply C.germFrame_mapsTo
    have corner := congrArg Subtype.val (C.linkCornerIndex_spec retain v chain covers q)
    change (chain.point (C.linkCornerIndex retain v chain covers q)).val.1 = q.val at corner
    rw [corner]
    exact x.property⟩

theorem tangentSectorPoint_isometry {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (covers : ∀ p, chain.Visited p) (q : C.CornerAt retain v) :
    Isometry (C.tangentSectorPoint retain v chain covers q) := by
  intro x y
  exact (C.germFrame (chain.point (C.linkCornerIndex retain v chain covers q)).val).isometry
    x.val y.val

def tangentCellToAngular {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (covers : ∀ p, chain.Visited p) (q : C.CornerAt retain v)
    (x : C.TangentCell retain v q) : (C.linkAngularFan retain v chain).Surface :=
  (C.linkAngularFan retain v chain).faceMap (C.linkCornerIndex retain v chain covers q)
    (C.tangentSectorPoint retain v chain covers q x)

theorem tangentCellToAngular_lipschitz {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (covers : ∀ p, chain.Visited p) (q : C.CornerAt retain v) :
    LipschitzWith 1 (C.tangentCellToAngular retain v chain covers q) := by
  change LipschitzWith 1
    ((C.linkAngularFan retain v chain).faceMap (C.linkCornerIndex retain v chain covers q) ∘
      C.tangentSectorPoint retain v chain covers q)
  simpa only [one_mul] using
    ((C.linkAngularFan retain v chain).faceMap_lipschitz
      (C.linkCornerIndex retain v chain covers q)).comp
      (C.tangentSectorPoint_isometry retain v chain covers q).lipschitzWith

theorem tangentCellToAngular_of_coordinates {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (q : C.CornerAt retain v) (x : C.TangentCell retain v q)
    (i : Fin (n + 1)) (y : (C.linkAngularFan retain v chain).Cell i)
    (corner : q.val = (chain.point i).val.1)
    (coordinates : C.germFrame (chain.point i).val x.val = y.val) :
    C.tangentCellToAngular retain v chain covers q x =
      (C.linkAngularFan retain v chain).faceMap i y := by
  have index : C.linkCornerIndex retain v chain covers q = i := by
    apply (C.linkCornerEquiv retain v chain covers).symm_apply_eq.mpr
    exact Subtype.ext corner
  subst i
  apply congrArg ((C.linkAngularFan retain v chain).faceMap
    (C.linkCornerIndex retain v chain covers q))
  exact Subtype.ext coordinates

theorem angularToTangent_tangentCellToAngular {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (q : C.CornerAt retain v) (x : C.TangentCell retain v q) :
    C.angularToTangent retain v chain (C.tangentCellToAngular retain v chain covers q x) =
      C.tangentFaceMap retain v q x := by
  change C.angularToTangent retain v chain
    ((C.linkAngularFan retain v chain).faceMap (C.linkCornerIndex retain v chain covers q)
      (C.tangentSectorPoint retain v chain covers q x)) = _
  rw [C.angularToTangent_faceMap]
  apply C.linkCellToTangent_of_coordinates retain v chain _ _ q x
  · have same := congrArg Subtype.val (C.linkCornerIndex_spec retain v chain covers q)
    exact same.symm
  · rfl

end Unfoldings.TriangleComplex
