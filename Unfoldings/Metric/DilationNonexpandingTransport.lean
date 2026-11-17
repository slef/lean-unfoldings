module

public import Unfoldings.Metric.HalfOpenIntervalExtension

/-! Two nonexpanding maps preserve exact bank distances when spatial placement is unchanged. -/

@[expose] public section

namespace Unfoldings

/-- Transport a whole dilation through a nonexpanding map. An unchanged isometric
spatial placement supplies the reverse bound, including at both endpoints. -/
def dilationOfNonexpandingTransport {A X Y Z : Type*} [PseudoEMetricSpace A]
    [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]
    (g : A →ᵈ X) (f : X → Y) (bounded_f : LipschitzWith 1 f)
    (place : Y → Z) (bounded_place : LipschitzWith 1 place) (original : A → Z)
    (source_distance : ∀ s t, edist (original s) (original t) = edist (g s) (g t))
    (same : ∀ t, place (f (g t)) = original t) : A →ᵈ Y :=
  dilationOfIsometricLift g id isometry_id (f ∘ g) (by
    intro s t
    apply le_antisymm
    · exact (bounded_f (g s) (g t)).trans_eq (one_mul _)
    · exact (source_distance s t).symm.trans_le
        ((congrArg₂ edist (same s) (same t)).symm.trans_le
          ((bounded_place (f (g s)) (f (g t))).trans_eq (one_mul _))))

end Unfoldings
