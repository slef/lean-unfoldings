module

public import Unfoldings.Metric.ClosedSeamOperations
public import Unfoldings.Metric.ChangeSeams
public import Unfoldings.Metric.Unglued
public import Unfoldings.Metric.BallChartTransport

/-! Whole metric balls in internally glued pieces retain their original piece metrics. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {I : Type*} (X : I → Type*) [∀ i, EMetricSpace (X i)]

/-- Different unjoined pieces are infinitely far apart, so every finite ball stays in one piece. -/
def emptyPieceBall (i : I) (x : X i) (r : ℝ) :
    Metric.eball x (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (of X (fun _ _ => False) i x) (ENNReal.ofReal r) := by
  let f : Metric.eball x (ENNReal.ofReal r) →
      Metric.eball (of X (fun _ _ => False) i x) (ENNReal.ofReal r) := fun y =>
    ⟨of X (fun _ _ => False) i y.val, by
      rw [Metric.mem_eball, edist_of_empty]
      exact y.property⟩
  have isometric : Isometry f := fun y z => edist_of_empty X i y.val z.val
  have onto : Function.Surjective f := by
    intro y
    obtain ⟨⟨j, q⟩, equal⟩ := point_surjective X (fun _ _ => False) y.val
    have near : edist (of X (fun _ _ => False) j q)
        (of X (fun _ _ => False) i x) < ENNReal.ofReal r := by
      exact (congrArg (fun z => edist z (of X (fun _ _ => False) i x)) equal).trans_lt
        y.property
    by_cases same : j = i
    · subst j
      refine ⟨⟨q, ?_⟩, Subtype.ext equal⟩
      exact (edist_of_empty X i q x).symm.trans_lt near
    · rw [edist_of_empty_of_ne X same] at near
      exact (not_lt_of_ge le_top near).elim
  exact ⟨Equiv.ofBijective f ⟨isometric.injective, onto⟩, isometric⟩

variable {J : I → Type*} (E : ∀ i, J i → Type*) [Finite I]
  [∀ i j, MetricSpace (E i j)] (S : ∀ i, ClosedSeams (E i))

/-- Flattened internal seams recover the disjoint union of the original intrinsic pieces. -/
def internalFamilyIsometry :
    Realization (NestedCell E) (ClosedSeams.ofFamily E S).relation ≃ᵢ
      Realization (fun i => Realization (E i) (S i).relation) (fun _ _ => False) :=
  (changeSeamsIsometryEquiv _
    (by
      intro x y joined
      obtain ⟨i, a, b, seam, rfl, rfl⟩ := (ClosedSeams.ofFamily_relation E S x y).mp joined
      exact point_eq_of_glue _ (NestedGlue.inside (inner := fun i => (S i).relation) i a b seam))
    (by
      intro x y joined
      cases joined with
      | inside i a b seam =>
        exact point_eq_of_glue _ ((ClosedSeams.ofFamily_relation E S _ _).mpr
          ⟨i, a, b, seam, rfl, rfl⟩)
      | between _ _ seam => exact seam.elim)).trans
    (nestedIsometryEquiv E (fun i => (S i).relation) (fun _ _ => False))

/-- Every original cell representative has exactly its original piece's whole finite ball. -/
def internalFamilyCellBall (i : I) (j : J i) (p : E i j) (r : ℝ) :
    Metric.eball (of (E i) (S i).relation j p) (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (of (NestedCell E) (ClosedSeams.ofFamily E S).relation ⟨i, j⟩ p)
        (ENNReal.ofReal r) :=
  (emptyPieceBall (fun i => Realization (E i) (S i).relation) i
    (of (E i) (S i).relation j p) r).trans
    (Unfoldings.isometryEquivEBall (internalFamilyIsometry E S).symm
      (of (fun i => Realization (E i) (S i).relation) (fun _ _ => False) i
        (of (E i) (S i).relation j p)) (ENNReal.ofReal r))

end Unfoldings.MetricGluing
