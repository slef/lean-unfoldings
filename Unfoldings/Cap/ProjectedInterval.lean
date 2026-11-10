module

public import Unfoldings.Cap.ProjectedFlatness
public import Unfoldings.Cap.GermSupports
public import Unfoldings.Polyhedron.IntervalLink
public import Unfoldings.Geometry.PlanarConeOrientation

/-! Actual interval-link rays in the projected mesh and their consistent orientation. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {v : C.Vertex Set.univ} {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)

def projectedIntervalRay (i : Fin (n + 2)) : Plane :=
  Cap.horizontal (K.folding.intervalLinkRay c i)

@[simp] theorem projectedIntervalRay_castSucc (i : Fin (n + 1)) :
    K.projectedIntervalRay c i.castSucc = K.projectedGermRay (c.point i) := by
  rw [projectedIntervalRay, K.folding.intervalLinkRay_castSucc, K.horizontal_germDirection]

@[simp] theorem projectedIntervalRay_succ (i : Fin (n + 1)) :
    K.projectedIntervalRay c i.succ = K.projectedGermRay (C.linkTurn Set.univ v (c.point i)) := by
  rw [projectedIntervalRay, K.folding.intervalLinkRay_succ, K.horizontal_germDirection]

@[simp] theorem projectedIntervalRay_last : K.projectedIntervalRay c (Fin.last (n + 1)) =
    K.projectedGermRay (C.linkTurn Set.univ v c.last) := by
  rw [projectedIntervalRay, K.folding.intervalLinkRay_last, K.horizontal_germDirection]

theorem projectedGermRay_ne_zero (p : C.LinkGerm Set.univ v) : K.projectedGermRay p ≠ 0 := by
  intro zero
  have genuine := K.projectedGermRay_orient_ne_zero p
  rw [zero] at genuine
  simp only [orient, PiLp.zero_apply, sub_zero, zero_mul, sub_self, ne_eq,
    not_true_eq_false] at genuine

theorem projectedIntervalRay_ne_zero (i : Fin (n + 2)) : K.projectedIntervalRay c i ≠ 0 := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [K.projectedIntervalRay_last]
    exact K.projectedGermRay_ne_zero _
  · rw [K.projectedIntervalRay_castSucc]
    exact K.projectedGermRay_ne_zero _

theorem projectedInterval_cones_disjoint (covers : ∀ p, c.Visited p) :
    Pairwise (fun i j : Fin (n + 1) => Disjoint
      (strictRayCone (K.projectedIntervalRay c i.castSucc) (K.projectedIntervalRay c i.succ))
      (strictRayCone (K.projectedIntervalRay c j.castSucc) (K.projectedIntervalRay c j.succ))) := by
  intro i j different
  rw [K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ,
    K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ,
    K.projectedGermRay_cone, K.projectedGermRay_cone]
  have face_ne : (c.point i).val.1.1 ≠ (c.point j).val.1.1 := by
    intro equal
    apply different
    apply (C.linkCornerEquiv Set.univ v c covers).injective
    apply K.cornerAt_face_injective v
    exact equal
  apply (K.projectedTriangle _).disjoint_cornerDirections (K.projectedTriangle _)
    (c.point i).val.1.2 (c.point j).val.1.2
  · exact (K.projectedGerm_apex (c.point i)).trans (K.projectedGerm_apex (c.point j)).symm
  · exact K.projectedTriangles_nonoverlapping face_ne

theorem projectedInterval_orient_sign (covers : ∀ p, c.Visited p) (i : Fin (n + 1)) :
    (0 < orient 0 (K.projectedIntervalRay c i.castSucc) (K.projectedIntervalRay c i.succ)) ↔
      0 < orient 0 (K.projectedIntervalRay c (0 : Fin (n + 1)).castSucc)
        (K.projectedIntervalRay c (0 : Fin (n + 1)).succ) := by
  apply interval_cone_orient_sign (K.projectedIntervalRay c) _
    (K.projectedInterval_cones_disjoint c covers) i
  intro j
  rw [K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ]
  exact K.projectedGermRay_orient_ne_zero (c.point j)

theorem sum_projectedInterval_angles (covers : ∀ p, c.Visited p) :
    (∑ i : Fin (n + 1), InnerProductGeometry.angle (K.projectedIntervalRay c i.castSucc)
      (K.projectedIntervalRay c i.succ)) = K.projectedTotalAngle Set.univ v := by
  simp only [K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ, K.projectedGermRay_angle]
  exact K.projectedLinkFan_totalAngle c covers

end Unfoldings.ConvexCap
