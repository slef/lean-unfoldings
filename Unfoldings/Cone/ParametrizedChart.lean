module

public import Unfoldings.Cone.SpatialParametrization
public import Unfoldings.Cone.Charts
public import Unfoldings.Complex.Regular
public import Unfoldings.Metric.BallIsometry

/-! A constructed planar tangent parametrization gives a whole intrinsic vertex chart. -/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} {v : C.Vertex Set.univ}

theorem TangentParametrization.isRegularPoint (A : F.TangentParametrization v)
    (embedded : F.IsEmbedded) : C.IsRegularPoint Set.univ (C.vertexPoint Set.univ v) := by
  let N := F.tangentChart Set.univ v
  let e := (A.isometryEquiv embedded).symm
  let p := e (C.tangentOrigin Set.univ v)
  let balls := basedEBallIsometry e (C.tangentOrigin Set.univ v) p rfl
    (ENNReal.ofReal N.radius)
  have near (z : Plane) : edist z p < ENNReal.ofReal N.radius ↔ dist z p < N.radius := by
    rw [edist_dist]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg
  let same : Metric.eball p (ENNReal.ofReal N.radius) ≃ᵢ Metric.ball p N.radius :=
    { toFun := fun z => ⟨z.val, (near z.val).mp z.property⟩
      invFun := fun z => ⟨z.val, (near z.val).mpr z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      isometry_toFun := fun _ _ => rfl }
  exact ⟨N.radius, N.positive, p, ⟨N.chart.symm.trans (balls.trans same)⟩⟩

end Unfoldings.SpatialFolding
