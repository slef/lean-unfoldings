module

public import Unfoldings.Geometry.SpatialEnvelopeFaceSideBall
public import Unfoldings.Geometry.TriangleContinuousExt
public import Unfoldings.Complex.Folding
public import Unfoldings.Metric.PhysicalCutCopyEquality

/-! Continuous lifts of whole physical faces into the same original cut agree exactly. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u v w

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]

theorem cut_eq_of_restore_eq_outside (cuts : Set Plane) (x y : P.Cut cuts)
    (same : (P.restoreCut cuts x).val = (P.restoreCut cuts y).val)
    (outside : Cap.horizontal (P.restoreCut cuts x).val ∉ cuts) : x = y := by
  apply (P.cutIsometryEquiv cuts).injective
  apply MetricGluing.cut_eq_of_fold_eq_outside P.spatialCell P.isClosed_spatialCell
    (Cap.horizontal ⁻¹' cuts)
  · exact (P.fold_cutIsometryEquiv cuts x).trans
      (same.trans (P.fold_cutIsometryEquiv cuts y).symm)
  · exact Eq.mpr (congrArg (fun z : Space => Cap.horizontal z ∉ cuts)
      (P.fold_cutIsometryEquiv cuts x)) outside

/-- A closed triangle's intrinsic side is fixed by its continuous uncut interior lift. -/
theorem continuous_triangle_cut_lifts_eq (cuts : Set Plane) (T : Triangle)
    (f g : T.Cell → P.Cut cuts) (first : Continuous f) (last : Continuous g)
    (same : ∀ x, (P.restoreCut cuts (f x)).val = (P.restoreCut cuts (g x)).val)
    (outside : ∀ x : T.Cell, x.val ∈ interior T.carrier →
      Cap.horizontal (P.restoreCut cuts (f x)).val ∉ cuts) : f = g := by
  apply T.continuous_ext_on_interior f g first last
  intro x inside
  exact P.cut_eq_of_restore_eq_outside cuts (f x) (g x) (same x) (outside x inside)

/-- Actual spatial coordinates and continuous whole-face lifts determine all original cut copies.
Only the interiors must avoid cuts; all closed bank and vertex copies follow by continuity. -/
theorem continuous_cut_lifts_eq {Face : Type v} [Fintype Face]
    {C : TriangleComplex.{v, w} Face} (F : SpatialFolding C) (retain : Set C.Seam)
    (cuts : Set Plane) (f g : C.Realization retain → P.Cut cuts)
    (first : Continuous f) (last : Continuous g)
    (first_fold : ∀ x, (P.restoreCut cuts (f x)).val = F.toSpace retain x)
    (last_fold : ∀ x, (P.restoreCut cuts (g x)).val = F.toSpace retain x)
    (outside : ∀ i, Disjoint (interior (C.triangle i).carrier)
      (F.place i ⁻¹' (Cap.horizontal ⁻¹' cuts))) : f = g := by
  funext x
  obtain ⟨⟨i, y⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) x
  have maps := P.continuous_triangle_cut_lifts_eq cuts (C.triangle i)
    (f ∘ C.faceMap retain i) (g ∘ C.faceMap retain i)
    (first.comp (C.faceMap_lipschitz retain i).continuous)
    (last.comp (C.faceMap_lipschitz retain i).continuous)
    (fun y => (first_fold (C.faceMap retain i y)).trans (last_fold (C.faceMap retain i y)).symm)
    (fun y inside => Eq.mpr (congrArg (fun z : Space => Cap.horizontal z ∉ cuts)
      (first_fold (C.faceMap retain i y))) (Set.disjoint_left.mp (outside i) inside))
  exact congrFun maps y

end Unfoldings.SpatialEnvelope.WholePartition
