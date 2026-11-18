module

public import Unfoldings.Geometry.RayWindowTrimming
public import Unfoldings.Geometry.SourceStartRadialPerturbation
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-! Actual internal-ray comparisons are continuous even when an endpoint is the source. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane (n + 2)) (source : Plane)

/-- Only the internal vertices must avoid the source; endpoint vertices are omitted. -/
theorem continuousAt_internalSourceAngleSum
    (genuine : ∀ i, P.internalSourceRay source i ≠ 0) :
    ContinuousAt (fun q => ∑ k : Fin n, InnerProductGeometry.angle
      (P.internalSourceRay q k.castSucc) (P.internalSourceRay q k.succ)) source := by
  classical
  have each (k : Fin n) : ContinuousAt (fun q => InnerProductGeometry.angle
      (P.internalSourceRay q k.castSucc) (P.internalSourceRay q k.succ)) source := by
    let a := P.vertex k.castSucc.succ.castSucc
    let b := P.vertex k.succ.succ.castSucc
    have pair : ContinuousAt (fun q : Plane => (a - q, b - q)) source :=
      (continuous_const.sub continuous_id).continuousAt.prodMk
        (continuous_const.sub continuous_id).continuousAt
    have angle : ContinuousAt (fun z : Plane × Plane => InnerProductGeometry.angle z.1 z.2)
        (a - source, b - source) :=
      InnerProductGeometry.continuousAt_angle (genuine k.castSucc) (genuine k.succ)
    change ContinuousAt (fun q : Plane => InnerProductGeometry.angle (a - q) (b - q)) source
    exact angle.comp (f := fun q : Plane => (a - q, b - q)) pair
  have finite_sum (s : Finset (Fin n)) : ContinuousAt (fun q => ∑ k ∈ s,
      InnerProductGeometry.angle (P.internalSourceRay q k.castSucc)
        (P.internalSourceRay q k.succ)) source := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (continuousAt_const (y := (0 : ℝ)))
    | @insert k s absent previous =>
      simp only [Finset.sum_insert absent]
      convert (each k).add previous using 1
  exact finite_sum Finset.univ

end Unfoldings.PolygonalChain
