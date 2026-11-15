module

public import Unfoldings.Metric.PolygonalCut
public import Unfoldings.Metric.Reparametrize

/-! Physical cut metrics commute with closed isometric embeddings of their ambient space. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

namespace PhysicalSeams

variable {I X : Type*} [Finite I] [MetricSpace X] {cells : I → Set X} (S : PhysicalSeams cells)

/-- A physical attachment means equal coordinates on exactly the specified closed carrier. -/
theorem relation_iff (a b : Total (fun i => cells i)) :
    S.relation a b ↔ a.2.val = b.2.val ∧ a.2.val ∈ S.carrier a.1 b.1 := by
  constructor
  · rintro ⟨p, x, rfl, rfl⟩
    exact ⟨rfl, x.property⟩
  · rintro ⟨same, member⟩
    refine ⟨(a.1, b.1), ⟨a.2.val, member⟩, rfl, ?_⟩
    exact congrArg (Sigma.mk b.1) (Subtype.ext same.symm)

end PhysicalSeams

variable {E F I : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [CompleteSpace E] [Finite I]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i)) (f : E → F) (isometric : Isometry f)

/-- Each actual cell and its isometric image have the same original Euclidean metric. -/
def isometricImageCell (i : I) : cells i ≃ᵢ (f '' cells i) where
  toEquiv := Equiv.ofBijective
    (fun x => (⟨f x.val, x.val, x.property, rfl⟩ : f '' cells i)) (by
      constructor
      · intro x y equal
        exact Subtype.ext (isometric.injective (congrArg Subtype.val equal))
      · rintro ⟨y, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩)
  isometry_toFun x y := isometric x.val y.val

include closed isometric in
omit [Finite I] in
theorem isClosed_isometricImageCell (i : I) : IsClosed (f '' cells i) :=
  isometric.isClosedEmbedding.isClosedMap _ (closed i)

omit [Finite I] in
/-- Closing each uncut attachment commutes with the original spatial isometric embedding. -/
theorem cutSeams_isometricImage_carrier (cuts : Set F) (i j : I) :
    (cutSeams (fun i => f '' cells i)
      (isClosed_isometricImageCell cells closed f isometric) cuts).carrier i j =
        f '' (cutSeams cells closed (f ⁻¹' cuts)).carrier i j := by
  change closure (((f '' cells i) ∩ (f '' cells j)) \ cuts) =
    f '' closure ((cells i ∩ cells j) \ f ⁻¹' cuts)
  rw [← Set.image_inter isometric.injective, ← Set.image_sdiff_preimage]
  exact isometric.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous
    isometric.continuous _

/-- The exact pulled-back attachment relation, with no added metric identifications. -/
theorem cutSeams_isometricImage_relation_iff (cuts : Set F)
    (a b : Total (fun i => cells i)) :
    reparametrizeGlue (isometricImageCell cells f isometric)
      (cutSeams (fun i => f '' cells i) (isClosed_isometricImageCell cells closed f isometric)
        cuts).relation a b ↔ (cutSeams cells closed (f ⁻¹' cuts)).relation a b := by
  rw [reparametrizeGlue, PhysicalSeams.relation_iff, PhysicalSeams.relation_iff]
  change (f a.2.val = f b.2.val ∧ f a.2.val ∈
    (cutSeams (fun i => f '' cells i) (isClosed_isometricImageCell cells closed f isometric)
      cuts).carrier a.1 b.1) ↔ _
  rw [cutSeams_isometricImage_carrier cells closed f isometric]
  simp only [isometric.injective.eq_iff, Set.mem_image, exists_eq_right]

/-- Isometric physical placement preserves the entire cut metric, including unbounded ends. -/
def cutIsometricImageEquiv (cuts : Set F) :
    PolygonalCut cells closed (f ⁻¹' cuts) ≃ᵢ
      PolygonalCut (fun i => f '' cells i)
        (isClosed_isometricImageCell cells closed f isometric) cuts :=
  (changeSeamsIsometryEquiv (fun i => cells i)
    (fun a b joined => point_eq_of_glue _
      ((cutSeams_isometricImage_relation_iff cells closed f isometric cuts a b).mpr joined))
    (fun a b joined => point_eq_of_glue _
      ((cutSeams_isometricImage_relation_iff cells closed f isometric cuts a b).mp joined))).trans
    (reparametrizeIsometryEquiv (isometricImageCell cells f isometric)
      (cutSeams (fun i => f '' cells i) (isClosed_isometricImageCell cells closed f isometric)
        cuts).relation)

@[simp] theorem cutIsometricImageEquiv_of (cuts : Set F) (i : I) (x : cells i) :
    cutIsometricImageEquiv cells closed f isometric cuts
      (of (fun i => cells i) (cutSeams cells closed (f ⁻¹' cuts)).relation i x) =
      of (fun i => f '' cells i)
        (cutSeams (fun i => f '' cells i) (isClosed_isometricImageCell cells closed f isometric)
          cuts).relation i (isometricImageCell cells f isometric i x) := rfl


/-- The exact image-cut isometry preserves the original physical placement of every point. -/
@[simp] theorem fold_cutIsometricImageEquiv (cuts : Set F)
    (x : PolygonalCut cells closed (f ⁻¹' cuts)) :
    (cutSeams (fun i => f '' cells i)
      (isClosed_isometricImageCell cells closed f isometric) cuts).fold
      (cutIsometricImageEquiv cells closed f isometric cuts x) =
        f ((cutSeams cells closed (f ⁻¹' cuts)).fold x) := by
  obtain ⟨a, rfl⟩ := point_surjective (fun i => cells i)
    (cutSeams cells closed (f ⁻¹' cuts)).relation x
  rfl

end Unfoldings.MetricGluing
