module

public import Unfoldings.FewestNets.ThreeExitGraftPhysicalAddresses

/-! At a terminal join the two legitimate original addresses name the same stack. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : FewestNets.ThreeExitStemWindows}
  {R : K.ThreeExitComponentRouting seed B compact nonempty H}

local notation "U" => K.selectionComponent slopes seed
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ K.restrictedCarrier U}
local notation "G" => SlopeEnvelope.recenter
  (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty) B.reference
local notation "pointOf" => (fun v : V => K.projectedVertex (Subtype.val v))

variable {level : ℝ}
  {M : (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel}
  (L : R.FloorWindowModel level M)

local notation "T[" h "]" => R.fineMesh level M h
local notation "D[" h "]" => SpatialEnvelope.FloorMesh.pairedComplex T[h]
local notation "F[" h "]" => R.fineMeshForest level M h
local notation "Sel[" h "]" => PotentialCutForest.selection F[h]

local instance graftTerminalAddressIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
    Fintype (T[h]).Index := @Fintype.ofFinite _ (T[h]).finite

variable (S : SourceContour (R := R) (M := M) (level := level))

local notation "T" => T[S.higher]
local notation "D" => D[S.higher]
local notation "Fcut" => F[S.higher]
local notation "Selection" => Sel[S.higher]
local notation "Attachment" => PotentialCutForest.ContourAttachment Fcut
local notation "Param" => PotentialCutForest.contourAttachmentParameter Fcut

local notation "restore" =>
  SpatialEnvelope.WholePartition.restoreCut L.whole.partition R.wholeCarrier

local notation "Child" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Exit" => TriangleComplex.ContourTerminalEdge D Selection
local notation "Root" => {v : V // v ∈ R.stems.choice.parents.roots}
local notation "Q" => SpatialEnvelope.FloorMesh.roof T
  (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M S.higher)
local notation "vertex" => ConvexRoof.projectedVertex Q
local notation "parent" => AscendingParents.parent (PotentialCutForest.parents Fcut)

local notation "Phys" => contourPhysicalAddress L S
local notation "FiniteEnd[" e "]" => (Sum.inl (Subtype.mk (Subtype.val e) (And.left (Subtype.property e))) : Attachment)

/-- The start of the continued ray is the literal endpoint of its finite bank. -/
theorem contourPhysicalAddress_tail_zero (e : Exit) :
    Phys (.inr e) 0 = Phys FiniteEnd[e] 1 :=
  congrArg (fun x : L.whole.Cut => Cap.horizontal (restore x).val)
    (L.contourBaseMark_tail_zero S e false)

set_option maxHeartbeats 1400000 in
/-- Two joined tails with the same physical start have the same terminal edge. -/
theorem contourPhysicalAddress_tail_zero_injective :
    Function.Injective fun e : Exit => Phys (.inr e) 0 := by
  intro e f equal
  obtain ⟨r, first, first_nonneg, first_lt, _, _, ray_e⟩ :=
    L.exists_contourPhysicalAddress_tail_ray S e
  obtain ⟨r', first', first'_nonneg, first'_lt, _, _, ray_f⟩ :=
    L.exists_contourPhysicalAddress_tail_ray S f
  let τ := R.exits.timeAtLevel level (R.exitRoot r)
  let τ' := R.exits.timeAtLevel level (R.exitRoot r')
  have at_e : Phys (.inr e) 0 = R.exits.ray (R.exitRoot r) τ := by
    have h := ray_e 0
    change Phys (.inr e) 0 = R.exits.ray (R.exitRoot r) (τ + (τ - first) * (0 : ℝ)) at h
    simpa only [mul_zero, add_zero] using h
  have at_f : Phys (.inr f) 0 = R.exits.ray (R.exitRoot r') τ' := by
    have h := ray_f 0
    change Phys (.inr f) 0 = R.exits.ray (R.exitRoot r') (τ' + (τ' - first') * (0 : ℝ)) at h
    simpa only [mul_zero, add_zero] using h
  have same_root : r' = r := by
    by_contra different
    exact Set.disjoint_left.mp (R.exit_rays_disjoint (R.exitRoot_injective.ne different))
      ⟨_, first'_nonneg.trans_lt first'_lt, at_f⟩
      ⟨_, first_nonneg.trans_lt first_lt, equal.symm.trans at_e⟩
  subst r'
  have d_e := sub_pos.mpr first_lt
  have d_f := sub_pos.mpr first'_lt
  let t : ℝ≥0 := ⟨(τ - first)⁻¹, (inv_pos.mpr d_e).le⟩
  let s : ℝ≥0 := ⟨(τ - first')⁻¹, (inv_pos.mpr d_f).le⟩
  have extra_e : Phys (.inr e) t = R.exits.ray (R.exitRoot r) (τ + 1) := by
    rw [ray_e]
    change R.exits.ray (R.exitRoot r) (τ + (τ - first) * (τ - first)⁻¹) = _
    rw [mul_inv_cancel₀ d_e.ne']
  have extra_f : Phys (.inr f) s = R.exits.ray (R.exitRoot r) (τ + 1) := by
    rw [ray_f]
    change R.exits.ray (R.exitRoot r) (τ + (τ - first') * (τ - first')⁻¹) = _
    rw [mul_inv_cancel₀ d_f.ne']
  have named := L.contourPhysicalAddress_eq_positiveTail S e t (inv_pos.mpr d_e)
    (.inr f) s (extra_f.trans extra_e.symm)
  exact (Sum.inr.inj (congrArg (fun z : Σ a : Attachment, Param a => z.1) named)).symm

set_option maxHeartbeats 1400000 in
/-- The only addresses of a terminal join are the end of its fine edge and
the zero parameter on the continued tail. -/
theorem contourPhysicalAddress_eq_terminalJoin (e : Exit) (a : Attachment) (s : Param a)
    (equal : Phys a s = Phys (.inr e) 0) :
    (⟨a, s⟩ : Σ a : Attachment, Param a) = ⟨FiniteEnd[e], 1⟩ ∨
      (⟨a, s⟩ : Σ a : Attachment, Param a) = ⟨.inr e, 0⟩ := by
  obtain ⟨speed, _, height⟩ := L.exists_contourPhysicalAddress_tail_height S e
  have at_join : (G).height (Phys (.inr e) 0) = level := by
    have h := height 0
    change (G).height (Phys (.inr e) 0) = level + speed * (0 : ℝ) at h
    simpa only [mul_zero, add_zero] using h
  have at_s : (G).height (Phys a s) = level := (congrArg (G).height equal).trans at_join
  cases a with
  | inr f =>
    obtain ⟨c, c_pos, speed_f⟩ := L.exists_contourPhysicalAddress_tail_height S f
    have zero : s = 0 := by
      by_contra positive
      have t_pos : 0 < s := lt_of_le_of_ne zero_le (Ne.symm positive)
      rw [speed_f] at at_s
      linarith only [at_s, mul_pos c_pos t_pos]
    subst s
    have same := L.contourPhysicalAddress_tail_zero_injective S equal
    subst f
    exact Or.inr rfl
  | inl f =>
    have end_time : s = 1 := by
      by_contra short
      by_cases source : s = 0
      · subst s
        rw [L.contourPhysicalAddress_finite S] at at_s
        change (G).height (AffineMap.lineMap (vertex f.val) (vertex (parent f.val)) (0 : ℝ)) =
          level at at_s
        rw [AffineMap.lineMap_apply_zero] at at_s
        exact (contourParentStart_below S f).ne at_s
      · have lower : 0 < s := lt_of_le_of_ne s.property.1 (Ne.symm source)
        have upper : s < 1 := lt_of_le_of_ne s.property.2 short
        exact (L.contourPhysicalAddress_finite_lt S f s ⟨lower, upper⟩).ne at_s
    subst s
    have at_parent := at_s
    rw [L.contourPhysicalAddress_finite S] at at_parent
    change (G).height (AffineMap.lineMap (vertex f.val) (vertex (parent f.val)) (1 : ℝ)) =
      level at at_parent
    rw [AffineMap.lineMap_apply_one] at at_parent
    have rooted : parent f.val ∈ (Fcut).parents.roots := by
      by_contra unrooted
      exact (contourParentStart_below S ⟨parent f.val, unrooted⟩).ne at_parent
    let terminal : Exit := ⟨f.val, f.property, rooted⟩
    have same := L.contourPhysicalAddress_tail_zero_injective S
      ((L.contourPhysicalAddress_tail_zero S terminal).trans equal)
    have same_vertex : f.val = e.val := congrArg (fun j : Exit => j.val) same
    have same_child : f = ⟨e.val, e.property.1⟩ := Subtype.ext same_vertex
    subst f
    exact Or.inl rfl

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
