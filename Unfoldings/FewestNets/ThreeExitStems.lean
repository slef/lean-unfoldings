module

public import Unfoldings.FewestNets.ThreeExitCutDisk
public import Unfoldings.FewestNets.ThreeExitHeadings
public import Unfoldings.Roof.SelectedDirectionEdge

/-! Choose both diagonal stems among the original seams of a selector component. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open FewestNets InnerProductGeometry Real Relation

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C) {slopes : Set Plane} (seed : Face)

local notation "U" => K.selectionComponent slopes seed
local notation "S" => K.restrictedCarrier U
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ S}
local notation "p" => (fun v : V => K.projectedVertex (Subtype.val v))

/-- The two possible parent seams have literal angle bounds in their respective
charts and stay inside the selected component. -/
structure ThreeExitComponentStems (δ : ℝ) extends K.ThreeExitComponentChoices
    (slopes := slopes) seed where
  east_segment : ∀ v ∉ choice.boundary, segment ℝ (p v) (p (choice.eastParent v)) ⊆ S
  west_segment : ∀ v ∉ choice.boundary, segment ℝ (p v) (p (choice.westParent v)) ⊆ S
  height_eq : ∀ v, choice.height v = p v 1
  east_heading : ∀ v ∉ choice.boundary,
    (exitHeadingChart false (p (choice.eastParent v) - p v)).arg ∈ Set.Icc δ (π / 2 - δ)
  west_heading : ∀ v ∉ choice.boundary,
    (exitHeadingChart true (p (choice.westParent v) - p v)).arg ∈ Set.Icc δ (π / 2 - δ)

/-- If the projected corners have margin `2 * δ` from a right angle,
each interior vertex has both diagonal parent seams. The exits at the
frontier can be assigned after the same two independent choices. -/
theorem exists_threeExitComponentStems {δ : ℝ} (positive : 0 < δ)
    (angles : ∀ f ∈ U, ∀ i, (K.projectedTriangle f).cornerAngle i ≤ π / 2 - 2 * δ)
    (eastAvailable westAvailable : V → Prop)
    (available : ∀ v : V, p v ∈ frontier S → eastAvailable v ∨ westAvailable v) :
    ∃ R : K.ThreeExitComponentStems (slopes := slopes) seed δ,
      R.choice.eastAvailable = eastAvailable ∧ R.choice.westAvailable = westAvailable := by
  classical
  let roots : Set V := {v | p v ∈ frontier S}
  have find (west : Bool) (v : {v : V // v ∉ roots}) :
      ∃ (w : V) (e : C.Seam),
        C.seamGraph.IsLink e v.val.val w.val ∧
        segment ℝ (p v.val) (p w) ⊆ S ∧
        0 < (p w - p v.val) 1 ∧
        (exitHeadingChart west (p w - p v.val)).arg ∈ Set.Icc δ (π / 2 - δ) := by
    let d := (exitHeadingChart west).symm (polarRay (π / 4))
    have d_ne : d ≠ 0 := by simpa [d] using polarRay_ne_zero (π / 4)
    have inside : p v.val ∈ interior S := by
      by_contra outside
      exact v.property ((mem_frontier_iff_notMem_interior v.val.property).mpr outside)
    obtain ⟨w, e, link, different, near, in_carrier⟩ := K.exists_selected_seam_near_direction
      U (β := π / 4 - δ) (fun f h i => by linarith only [angles f h i])
      v.val.val inside d d_ne
    let next : V := ⟨w, in_carrier (right_mem_segment ℝ _ _)⟩
    have genuine : p next - p v.val ≠ 0 := fun same =>
      different (K.projectedVertex_injective (sub_eq_zero.mp same))
    have heading := threeExit_heading_of_near_diagonal west genuine positive near
    exact ⟨next, e, link, in_carrier, (threeExit_stem_advances west genuine positive heading).2,
      heading⟩
  choose E Eedge Elink Esegment Eup Eheading using find false
  choose W Wedge Wlink Wsegment Wup Wheading using find true
  have applyE (v : V) (h : v ∉ roots) :
      (if a : v ∉ roots then E ⟨v, a⟩ else v) = E ⟨v, h⟩ := dif_pos h
  have applyW (v : V) (h : v ∉ roots) :
      (if a : v ∉ roots then W ⟨v, a⟩ else v) = W ⟨v, h⟩ := dif_pos h
  let choice : ThreeExitChoices V := {
    boundary := roots
    height := fun v => p v 1
    eastParent v := if h : v ∉ roots then E ⟨v, h⟩ else v
    westParent v := if h : v ∉ roots then W ⟨v, h⟩ else v
    east_up v h := by
      rw [applyE v h]
      exact sub_pos.mp (Eup ⟨v, h⟩)
    west_up v h := by
      rw [applyW v h]
      exact sub_pos.mp (Wup ⟨v, h⟩)
    eastAvailable := eastAvailable
    westAvailable := westAvailable
    available := available }
  refine ⟨{
    choice := choice
    roots_eq := rfl
    eastEdge := Eedge
    westEdge := Wedge
    east_link v := ?_
    west_link v := ?_
    east_segment v h := ?_
    west_segment v h := ?_
    height_eq v := rfl
    east_heading v h := ?_
    west_heading v h := ?_
    }, rfl, rfl⟩
  · simpa only [choice, applyE v.val v.property] using Elink v
  · simpa only [choice, applyW v.val v.property] using Wlink v
  · simpa only [choice, applyE v h] using Esegment ⟨v, h⟩
  · simpa only [choice, applyW v h] using Wsegment ⟨v, h⟩
  · simpa only [choice, applyE v h] using Eheading ⟨v, h⟩
  · simpa only [choice, applyW v h] using Wheading ⟨v, h⟩

end Unfoldings.ConvexRoof
