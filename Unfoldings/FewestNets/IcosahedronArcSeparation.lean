module

public import Unfoldings.FewestNets.IcosahedronArcIntersections
public import Unfoldings.FewestNets.IcosahedronMeshTilt
public import Unfoldings.Geometry.GnomonicArcSeparation
public import Unfoldings.Geometry.ShortMinorArcDiameter
public import Unfoldings.Geometry.EquatorialMinorArc
public import Unfoldings.Geometry.NorthFrame

/-! The endpoint guard suffices for the uniform separation of actual dual edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry Real

/-- A chart around a close pair of points on distinct nonincident arcs gives
a nearby endpoint pair, with at most 1.01 angular distortion. -/
theorem exists_near_endpoint_of_meshArc_proximity {q : ℕ}
    (qbig : 100 ≤ q) (hq : 0 < q) {e f : MeshEdge q} (different : e ≠ f)
    (no_common : ∀ a b, meshEndpoint hq e a ≠ meshEndpoint hq f b)
    {s : ℝ} (spos : 0 < s) (s_small : s ≤ icosahedronEdge / q)
    {x y : Space} (hx : x ∈ closedMinorArc (meshEndpoint hq e false) (meshEndpoint hq e true))
    (hy : y ∈ closedMinorArc (meshEndpoint hq f false) (meshEndpoint hq f true))
    (near : angle x y < s) :
    ∃ p ∈ closedMinorArc (meshEndpoint hq e false) (meshEndpoint hq e true),
      ∃ r ∈ closedMinorArc (meshEndpoint hq f false) (meshEndpoint hq f true),
        ((∃ a, p = meshEndpoint hq e a) ∨ (∃ b, r = meshEndpoint hq f b)) ∧
          angle p r < (101 / 100 : ℝ) * s := by
  let h := icosahedronEdge / q
  let c : ℝ := 997 / 1000
  let arc (a : MeshEdge q) := closedMinorArc (meshEndpoint hq a false) (meshEndpoint hq a true)
  have short (g : MeshEdge q) :=
    (meshEndpoint_angle_lt_pi_div_two qbig hq g).le
  have short' (g : MeshEdge q) :=
    (meshEndpoint_angle_lt_twice_step qbig hq g).le
  have hd : h < 3 / 250 := by
    have edge : icosahedronEdge < 6 / 5 := by
      have root : (10 / 3 : ℝ) < √((10 : ℝ) + 2 * √5) := by
        have lo : (2 : ℝ) ≤ √5 :=
          (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
        apply (Real.lt_sqrt (by norm_num)).mpr
        linarith only [lo]
      rw [icosahedronEdge, div_lt_iff₀ (by positivity)]
      linarith only [root]
    have qpos : (0 : ℝ) < q := by exact_mod_cast hq
    have qbound : (100 : ℝ) ≤ q := by exact_mod_cast qbig
    dsimp only [h]
    rw [div_lt_iff₀ qpos]
    linarith only [edge, qbound]
  have unit (g : MeshEdge q) (u : Space) (mem : u ∈ arc g) : ‖u‖ = 1 :=
    (meshEdge_sites_tied_of_mem_arc qbig hq g mem).1
  have extent (g : MeshEdge q) (u v : Space) (hu : u ∈ arc g) (hv : v ∈ arc g) :
      angle u v ≤ 4 * h := by
    have h := angle_le_twice_side_angle_of_mem_closedMinorArc (meshEndpoint_unit hq g false)
      (meshEndpoint_unit hq g true) (short g) hu hv
    linarith only [h, short' g]
  have close (z : Space) (hz : z ∈ arc e ∨ z ∈ arc f) : angle x z ≤ 5 * h := by
    rcases hz with he | hf
    · have base := extent e x z hx he
      linarith only [base, s_small, spos]
    · have base := extent f y z hy hf
      have tri := angle_le_angle_add_angle x y z
      linarith only [base, tri, near, s_small]
  let L := Cap.northFrame x
  have height (z : Space) (hz : z ∈ arc e ∨ z ∈ arc f) : c ≤ (L z) 2 := by
    have zu : ‖z‖ = 1 := hz.elim (unit e z) (unit f z)
    have at_most : angle x z ≤ 3 / 50 := (close z hz).trans (by linarith only [hd])
    have sq := (sq_le_sq₀ (angle_nonneg _ _) (by norm_num : (0 : ℝ) ≤ 3 / 50)).mpr at_most
    change c ≤ Cap.northFrame x z 2
    rw [Cap.northFrame_height x (unit e x hx), inner_eq_cos_angle_of_norm_eq_one (unit e x hx) zu]
    dsimp only [c]
    linarith only [sq, Real.one_sub_sq_div_two_le_cos (x := angle x z)]
  let slope (z : Space) : Plane := ((L z) 2)⁻¹ • Cap.horizontal (L z)
  have lift (z : Space) (hz : z ∈ arc e ∨ z ∈ arc f) : Cap.gnomonicNormal (slope z) = L z :=
    Cap.gnomonicNormal_slope _ ((L.norm_map z).trans (hz.elim (unit e z) (unit f z)))
      ((by norm_num : 0 < c).trans_le (height z hz))
  have endpoint_arc (g : MeshEdge q) (b : Bool) : meshEndpoint hq g b ∈ arc g := by
    cases b
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  let imageArc (g : MeshEdge q) := closedMinorArc
    (Cap.gnomonicNormal (slope (meshEndpoint hq g false)))
    (Cap.gnomonicNormal (slope (meshEndpoint hq g true)))
  have first_eq : L '' arc e = imageArc e := by
    dsimp only [arc, imageArc]
    rw [SpatialRotation.image_closedMinorArc_linearIsometry, lift _ (.inl (endpoint_arc e false)),
      lift _ (.inl (endpoint_arc e true))]
  have last_eq : L '' arc f = imageArc f := by
    dsimp only [arc, imageArc]
    rw [SpatialRotation.image_closedMinorArc_linearIsometry, lift _ (.inr (endpoint_arc f false)),
      lift _ (.inr (endpoint_arc f true))]
  have disjoint := disjoint_meshEdge_arcs_of_nonincident qbig hq different no_common
  have disjoint_image : Disjoint (imageArc e) (imageArc f) := by
    rw [← first_eq, ← last_eq]
    refine Set.disjoint_left.mpr ?_
    rintro w ⟨p, hp, ep⟩ ⟨r, hr, er⟩
    exact Set.disjoint_left.mp disjoint hp ((L.injective (ep.trans er.symm)).symm ▸ hr)
  have x_mem : L x ∈ imageArc e := first_eq ▸ ⟨x, hx, rfl⟩
  have y_mem : L y ∈ imageArc f := last_eq ▸ ⟨y, hy, rfl⟩
  obtain ⟨p', hp', r', hr', endpoint, bound⟩ := Cap.exists_arcEndpoint_pair_angle_le _ _ _ _
    disjoint_image x_mem y_mem (by norm_num : 0 < c) (by norm_num : c ≤ 1)
    (height x (.inl hx)) (height y (.inr hy))
  have p_image : p' ∈ L '' arc e := by
    rw [first_eq]
    exact hp'
  have r_image : r' ∈ L '' arc f := by
    rw [last_eq]
    exact hr'
  obtain ⟨p, hp, p_eq⟩ := p_image
  obtain ⟨r, hr, r_eq⟩ := r_image
  refine ⟨p, hp, r, hr, ?_, ?_⟩
  · rcases endpoint with at_p | at_p | at_r | at_r
    · exact .inl ⟨false, L.injective
        (p_eq.trans (at_p.trans (lift _ (.inl (endpoint_arc e false)))))⟩
    · exact .inl ⟨true, L.injective
        (p_eq.trans (at_p.trans (lift _ (.inl (endpoint_arc e true)))))⟩
    · exact .inr ⟨false, L.injective
        (r_eq.trans (at_r.trans (lift _ (.inr (endpoint_arc f false)))))⟩
    · exact .inr ⟨true, L.injective
        (r_eq.trans (at_r.trans (lift _ (.inr (endpoint_arc f true)))))⟩
  · rw [← p_eq, ← r_eq] at bound
    have moved : angle p r ≤ (c ^ 2)⁻¹ * angle x y := by
      change angle (L.toLinearIsometry p) (L.toLinearIsometry r) ≤
        (c ^ 2)⁻¹ * angle (L.toLinearIsometry x) (L.toLinearIsometry y) at bound
      simpa only [LinearIsometry.angle_map] using bound
    have factor : (c ^ 2)⁻¹ < (101 / 100 : ℝ) := by norm_num [c]
    exact moved.trans_lt ((mul_lt_mul_of_pos_left near (by positivity)).trans
      (mul_lt_mul_of_pos_right factor spos))

end Unfoldings.FewestNets.Icosahedron
