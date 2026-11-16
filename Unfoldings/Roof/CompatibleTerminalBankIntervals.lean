module

public import Unfoldings.Roof.CompatibleTerminalFiberBanks
public import Mathlib.Topology.Order.IntermediateValue

/-! Closed finite terminal-bank intervals are restrictions of the actual whole original banks. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  {M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel} (W : R.WholeCutModel M)

local instance terminalIntervalIndexFintype : Fintype W.Index := W.finiteIndex

/-- A continuous original finite terminal bank is the restriction of one named whole
bank, including its actual original endpoint copy at parameter zero. -/
theorem wholeTerminalBank_eq_on_Icc (r : {v // v ∈ R.parents.roots}) {T : ℝ} (positive : 0 < T)
    (curve : Set.Icc (0 : ℝ) T → W.Cut) (continuous : Continuous curve)
    (position : ∀ t, Cap.horizontal (W.partition.restoreCut R.carrier (curve t)).val =
      R.exterior.ray (R.terminalIndex r) t.val) :
    ∃ side : Bool, ∀ t, curve t =
      K.wholeTerminalBank compact nonempty R no_boundary W r side ⟨t.val, t.property.1⟩ := by
  let forward (t : Set.Ioc (0 : ℝ) T) : Set.Icc (0 : ℝ) T :=
    ⟨t.val, t.property.1.le, t.property.2⟩
  have continuous_forward : Continuous forward := continuous_subtype_val.subtype_mk _
  let time (t : Set.Ioc (0 : ℝ) T) : ℝ≥0 := ⟨t.val, t.property.1.le⟩
  let : PreconnectedSpace (Set.Ioc (0 : ℝ) T) := Subtype.preconnectedSpace isPreconnected_Ioc
  obtain ⟨side, same⟩ := K.wholeTerminalBank_side_constant compact nonempty R no_boundary W r
    (curve ∘ forward) (continuous.comp continuous_forward) time (fun t => t.property.1)
    (fun t => position (forward t))
  let bank (t : Set.Icc (0 : ℝ) T) :=
    K.wholeTerminalBank compact nonempty R no_boundary W r side ⟨t.val, t.property.1⟩
  have continuous_bank : Continuous bank :=
    (Dilation.lipschitzWith
      (K.wholeTerminalBank compact nonempty R no_boundary W r side)).continuous.comp
      (continuous_subtype_val.subtype_mk _)
  let S : Set (Set.Icc (0 : ℝ) T) := {t | 0 < t.val}
  have agrees : Set.EqOn curve bank S := by
    intro t ht
    exact same ⟨t.val, ht, t.property.2⟩
  have image : Subtype.val '' S = Set.Ioc (0 : ℝ) T := by
    ext t
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hq, q.property.2⟩
    · intro ht
      exact ⟨⟨t, ht.1.le, ht.2⟩, ht.1, rfl⟩
  refine ⟨side, fun t => agrees.closure continuous continuous_bank ?_⟩
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  change t.val ∈ closure (Subtype.val '' S)
  rw [image, closure_Ioc positive.ne]
  exact t.property

end Unfoldings.ConvexRoof
