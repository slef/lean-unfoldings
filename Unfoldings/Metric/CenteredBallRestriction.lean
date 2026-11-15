module

public import Unfoldings.Metric.BallChartTransport

/-! A centered whole-ball isometry restricts canonically to every smaller concentric ball. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings

variable {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]

/-- Restrict a centered intrinsic ball chart without losing whole-ball surjectivity. -/
def restrictCenteredEBallEquiv {x : X} {y : Y} {R r : ℝ≥0∞} (positive : 0 < R) (small : r ≤ R)
    (B : Metric.eball x R ≃ᵢ Metric.eball y R)
    (center : (B ⟨x, Metric.mem_eball_self positive⟩).val = y) :
    Metric.eball x r ≃ᵢ Metric.eball y r := by
  let root : Metric.eball x R := ⟨x, Metric.mem_eball_self positive⟩
  let map (z : Metric.eball x r) : Metric.eball y r :=
    ⟨(B ⟨z.val, z.property.trans_le small⟩).val, by
      have distance := B.isometry.edist_eq ⟨z.val, z.property.trans_le small⟩ root
      change edist (B ⟨z.val, z.property.trans_le small⟩).val (B root).val =
        edist z.val x at distance
      rw [center] at distance
      exact distance.trans_lt z.property⟩
  have isometric : Isometry map := fun z w =>
    B.isometry.edist_eq ⟨z.val, z.property.trans_le small⟩ ⟨w.val, w.property.trans_le small⟩
  have surjective : Function.Surjective map := by
    intro w
    let target : Metric.eball y R := ⟨w.val, w.property.trans_le small⟩
    let z := B.symm target
    have near : edist z.val x < r := by
      have distance := B.isometry.edist_eq z root
      rw [B.apply_symm_apply] at distance
      change edist w.val (B root).val =
        edist z.val x at distance
      rw [center] at distance
      exact distance.symm.trans_lt w.property
    refine ⟨⟨z.val, near⟩, ?_⟩
    apply Subtype.ext
    change (B ⟨z.val, near.trans_le small⟩).val = w.val
    exact congrArg (fun u : Metric.eball y R => u.val) (B.apply_symm_apply target)
  exact ⟨Equiv.ofBijective map ⟨isometric.injective, surjective⟩, isometric⟩

@[simp] theorem restrictCenteredEBallEquiv_val {x : X} {y : Y} {R r : ℝ≥0∞}
    (positive : 0 < R) (small : r ≤ R) (B : Metric.eball x R ≃ᵢ Metric.eball y R)
    (center : (B ⟨x, Metric.mem_eball_self positive⟩).val = y) (z : Metric.eball x r) :
    (restrictCenteredEBallEquiv positive small B center z).val =
      (B ⟨z.val, z.property.trans_le small⟩).val := rfl

end Unfoldings
