module

public import Unfoldings.FewestNets.CheckedPlane
public import Unfoldings.Geometry.CyclicConvexVertices

/-! Exact rational convexity tests for a cyclic progress-body vertex list. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

def rationalPolygonPoint (p : ℚ × ℚ) : Plane :=
  WithLp.toLp 2 ![(p.1 : ℝ), (p.2 : ℝ)]

theorem rationalPolygonPoint_injective : Function.Injective rationalPolygonPoint := by
  intro a b eq
  apply Prod.ext
  · have h := congrArg (fun p : Plane => p 0) eq
    change (a.1 : ℝ) = (b.1 : ℝ) at h
    exact_mod_cast h
  · have h := congrArg (fun p : Plane => p 1) eq
    change (a.2 : ℝ) = (b.2 : ℝ) at h
    exact_mod_cast h

def rationalOrient (p q r : ℚ × ℚ) : ℚ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

theorem orient_rationalPolygonPoint (p q r : ℚ × ℚ) :
    orient (rationalPolygonPoint p) (rationalPolygonPoint q) (rationalPolygonPoint r) =
      (rationalOrient p q r : ℝ) := by
  simp only [rationalPolygonPoint, orient, rationalOrient, Rat.cast_sub, Rat.cast_mul]
  rfl

/-- One exact test per incident pair of edges and per vertex against each
supporting side. Subsequent panel tests use the whole-body theorem. -/
def checkCyclicRationalBody {m : ℕ} (body : Fin m → ℚ × ℚ) (next : Equiv.Perm (Fin m)) : Bool :=
  (List.finRange m).all fun i =>
    decide (0 < rationalOrient (body (next.symm i)) (body i) (body (next i))) &&
    (List.finRange m).all fun j =>
      decide (0 ≤ rationalOrient (body i) (body (next i)) (body j))

theorem cyclicConvex_of_check {m : ℕ} (body : Fin m → ℚ × ℚ) (next : Equiv.Perm (Fin m))
    (passed : checkCyclicRationalBody body next = true) :
    CyclicConvexVertices (rationalPolygonPoint ∘ body) next := by
  have test (i : Fin m) := List.all_eq_true.mp passed i (List.mem_finRange i)
  constructor
  · intro i
    have h := test i
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have real_pos : 0 < orient (rationalPolygonPoint (body (next.symm i)))
        (rationalPolygonPoint (body i)) (rationalPolygonPoint (body (next i))) := by
      rw [orient_rationalPolygonPoint]
      exact_mod_cast h.1
    have eq (a b c : Plane) : orient 0 (b - a) (c - b) = orient a b c := by
      simp only [orient, PiLp.zero_apply, PiLp.sub_apply, sub_zero]
      ring
    change 0 < orient 0 (_ - _) (_ - _)
    rwa [eq]
  · intro i j
    have h := test i
    simp only [Bool.and_eq_true] at h
    have eq := of_decide_eq_true (List.all_eq_true.mp h.2 j (List.mem_finRange j))
    change 0 ≤ orient (rationalPolygonPoint (body i)) (rationalPolygonPoint (body (next i)))
      (rationalPolygonPoint (body j))
    rw [orient_rationalPolygonPoint]
    exact_mod_cast eq

end Unfoldings.FewestNets
