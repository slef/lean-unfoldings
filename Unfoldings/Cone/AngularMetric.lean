module

public import Unfoldings.Cone.AngularFan
public import Unfoldings.Metric.FiniteComponent

/-!
# The common apex and ordinary metric of a slit angular fan

Consecutive zero-radius seam identifications identify all apices. Exact
within-cell distances then give exact radial distance and finite distances
between every pair of points. No nonoverlap assumption is used.
-/

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n)

def origin : A.Surface := A.faceMap 0 (A.start 0 0)

theorem faceMap_start_zero (i : Fin (n + 1)) :
    A.faceMap i (A.start i 0) = A.origin := by
  induction i using Fin.inductionOn with
  | zero => rfl
  | succ i ih =>
    have joined : A.faceMap i.castSucc (A.finish i.castSucc 0) =
        A.faceMap i.succ (A.start i.succ 0) :=
      MetricGluing.point_eq_of_glue A.Cell ⟨i, 0, rfl, rfl⟩
    rw [A.finish_zero] at joined
    exact joined.symm.trans ih

@[simp] theorem develop_origin : A.develop A.origin = 0 := by
  rw [origin, A.develop_faceMap]
  simp [place, start]

theorem edist_origin_faceMap (i : Fin (n + 1)) (x : A.Cell i) :
    edist A.origin (A.faceMap i x) = edist (0 : ℂ) x.val := by
  rw [← A.faceMap_start_zero i]
  exact (A.faceMap_isometry i).edist_eq (A.start i 0) x

theorem edist_origin_ne_top (x : A.Surface) : edist A.origin x ≠ ⊤ := by
  obtain ⟨⟨i, p⟩, rfl⟩ := MetricGluing.point_surjective A.Cell A.glue x
  change edist A.origin (A.faceMap i p) ≠ ⊤
  rw [A.edist_origin_faceMap]
  exact edist_ne_top _ _

theorem edist_ne_top (x y : A.Surface) : edist x y ≠ ⊤ :=
  Unfoldings.finite_edist_trans
    (by simpa only [edist_comm] using A.edist_origin_ne_top x)
    (A.edist_origin_ne_top y)

/-- The constructed fan metric preserves the original edistance and topology. -/
@[instance_reducible] def metricSpace : MetricSpace A.Surface :=
  EMetricSpace.toMetricSpace A.edist_ne_top

attribute [instance] metricSpace

theorem dist_origin_faceMap (i : Fin (n + 1)) (x : A.Cell i) :
    dist A.origin (A.faceMap i x) = ‖x.val‖ := by
  have equal := congrArg ENNReal.toReal (A.edist_origin_faceMap i x)
  simpa only [edist_dist, dist_zero_left, ENNReal.toReal_ofReal dist_nonneg,
    ENNReal.toReal_ofReal (norm_nonneg _)] using equal

end Unfoldings.AngularFan
