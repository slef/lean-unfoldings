module

public import Unfoldings.Cone.Apex
public import Unfoldings.Metric.FiniteComponent
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Exact radial distance in the constructed tangent fan

Distance to the apex in each wedge is nonexpanding and agrees across the
actual radial seams. Its descended function supplies the matching lower bound
for the distance from the common origin.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

theorem tangentLeft_apex_endpoint (s : C.TangentSeam retain v) :
    (C.tangentApex retain v (C.tangentLeft retain v s)).val =
      ((C.triangle (C.seamSide s.val.1 s.val.2.1).face).endpoint
        (C.seamSide s.val.1 s.val.2.1).edge s.val.2.2).val := by
  obtain ⟨⟨s, side, b⟩, kept, central⟩ := s
  cases b <;> rfl

theorem tangentRight_apex_endpoint (s : C.TangentSeam retain v) :
    (C.tangentApex retain v (C.tangentRight retain v s)).val =
      ((C.triangle (C.seamSide s.val.1 (!s.val.2.1)).face).endpoint
        (C.seamSide s.val.1 (!s.val.2.1)).edge
        (C.acrossEndpoint s.val.1 s.val.2.1 s.val.2.2)).val := by
  have formula (T : Triangle) (e : Fin 3) (b : Bool) :
      (T.endpoint e b).val = T.vertex (if b then Triangle.next e else e) := by
    cases b <;> rfl
  exact (formula _ _ _).symm

theorem tangentRight_apex_across (s : C.TangentSeam retain v) :
    (C.tangentApex retain v (C.tangentRight retain v s)).val =
      (C.across s.val.1 s.val.2.1
        ((C.triangle (C.seamSide s.val.1 s.val.2.1).face).endpoint
          (C.seamSide s.val.1 s.val.2.1).edge s.val.2.2)).val :=
  (C.tangentRight_apex_endpoint retain v s).trans
    (congrArg Subtype.val (C.endpoint_acrossEndpoint s.val.1 s.val.2.1 s.val.2.2))

/-- The Euclidean radius in one original corner wedge. -/
def tangentCellRadius (c : C.CornerAt retain v) (x : C.TangentCell retain v c) : ℝ :=
  dist x (C.tangentApex retain v c)

theorem tangentCellRadius_lipschitz (c : C.CornerAt retain v) :
    LipschitzWith 1 (C.tangentCellRadius retain v c) :=
  LipschitzWith.dist_left (C.tangentApex retain v c)

/-- Original endpoint transport preserves radius at every nonnegative radial scale. -/
theorem tangentCellRadius_compatible : ∀ a b, C.tangentGlue retain v a b →
    C.tangentCellRadius retain v a.1 a.2 = C.tangentCellRadius retain v b.1 b.2 := by
  rintro a b ⟨s, x, t, nonnegative, rfl, rfl⟩
  change dist (AffineMap.lineMap
    (C.tangentApex retain v (C.tangentLeft retain v s)).val x.val t)
      (C.tangentApex retain v (C.tangentLeft retain v s)).val =
    dist (AffineMap.lineMap (C.tangentApex retain v (C.tangentRight retain v s)).val
      (C.across s.val.1 s.val.2.1 x).val t)
        (C.tangentApex retain v (C.tangentRight retain v s)).val
  rw [dist_lineMap_left, dist_lineMap_left]
  congr 1
  rw [C.tangentLeft_apex_endpoint, C.tangentRight_apex_across]
  exact ((C.across s.val.1 s.val.2.1).isometry.dist_eq _ x).symm

/-- The actual radius function on the metric separation quotient. -/
def tangentRadius : C.TangentFan retain v → ℝ :=
  MetricGluing.lift (C.TangentCell retain v) (C.tangentGlue retain v)
    (C.tangentCellRadius retain v) (C.tangentCellRadius_lipschitz retain v)
    (C.tangentCellRadius_compatible retain v)

@[simp] theorem tangentRadius_faceMap (c : C.CornerAt retain v) (x : C.TangentCell retain v c) :
    C.tangentRadius retain v (C.tangentFaceMap retain v c x) =
      C.tangentCellRadius retain v c x := rfl

theorem tangentRadius_lipschitz : LipschitzWith 1 (C.tangentRadius retain v) :=
  MetricGluing.lift_lipschitz (C.TangentCell retain v) (C.tangentGlue retain v)
    (C.tangentCellRadius retain v) (C.tangentCellRadius_lipschitz retain v)
    (C.tangentCellRadius_compatible retain v)

@[simp] theorem tangentRadius_origin : C.tangentRadius retain v (C.tangentOrigin retain v) = 0 := by
  obtain ⟨p⟩ := C.nonempty_linkGerm retain v
  let c : C.CornerAt retain v := ⟨p.val.1, p.property⟩
  rw [C.tangentOrigin_eq retain v c]
  exact (C.tangentRadius_faceMap retain v c (C.tangentApex retain v c)).trans (dist_self _)

theorem tangentRadius_nonneg (x : C.TangentFan retain v) : 0 ≤ C.tangentRadius retain v x := by
  obtain ⟨⟨c, x⟩, rfl⟩ := MetricGluing.point_surjective (C.TangentCell retain v)
    (C.tangentGlue retain v) x
  exact dist_nonneg

/-- The radial segment upper bound agrees with the radius-function lower bound. -/
theorem tangent_edist_origin_faceMap (c : C.CornerAt retain v) (x : C.TangentCell retain v c) :
    edist (C.tangentOrigin retain v) (C.tangentFaceMap retain v c x) =
      edist (C.tangentApex retain v c) x := by
  apply le_antisymm
  · rw [C.tangentOrigin_eq retain v c]
    exact MetricGluing.edist_of_le (C.TangentCell retain v) (C.tangentGlue retain v) c _ x
  · have bound := (C.tangentRadius_lipschitz retain v).edist_le_mul
      (C.tangentOrigin retain v) (C.tangentFaceMap retain v c x)
    simp only [ENNReal.coe_one, one_mul, C.tangentRadius_origin, C.tangentRadius_faceMap] at bound
    have lower : ENNReal.ofReal (dist x (C.tangentApex retain v c)) ≤
        edist (C.tangentOrigin retain v) (C.tangentFaceMap retain v c x) := by
      simpa only [tangentCellRadius, edist_dist, Real.dist_eq, zero_sub, abs_neg,
        abs_of_nonneg dist_nonneg] using bound
    rw [edist_dist, dist_comm]
    exact lower

theorem tangent_edist_origin_ne_top (x : C.TangentFan retain v) :
    edist (C.tangentOrigin retain v) x ≠ ⊤ := by
  obtain ⟨⟨c, x⟩, rfl⟩ := MetricGluing.point_surjective (C.TangentCell retain v)
    (C.tangentGlue retain v) x
  change edist (C.tangentOrigin retain v) (C.tangentFaceMap retain v c x) ≠ ⊤
  rw [C.tangent_edist_origin_faceMap]
  exact edist_ne_top _ _

theorem tangent_edist_ne_top (x y : C.TangentFan retain v) : edist x y ≠ ⊤ :=
  finite_edist_trans (by simpa only [edist_comm] using C.tangent_edist_origin_ne_top retain v x)
    (C.tangent_edist_origin_ne_top retain v y)

/-- The tangent fan has a canonical ordinary metric, preserving edistance and topology. -/
@[instance_reducible] def tangentMetricSpace : MetricSpace (C.TangentFan retain v) :=
  EMetricSpace.toMetricSpace (C.tangent_edist_ne_top retain v)

attribute [instance] tangentMetricSpace

end Unfoldings.TriangleComplex
